use prompt::{puzzle, welcome};

use halo2_proofs::arithmetic::PrimeField;
use halo2_proofs::circuit::{Layouter, SimpleFloorPlanner, Value};
use halo2_proofs::plonk::{
    create_proof as create_plonk_proof, keygen_pk, keygen_vk, verify_proof as verify_plonk_proof,
    Advice, Circuit, Column, ConstraintSystem, Error, Fixed, Instance, ProvingKey, VerifyingKey,
};
use halo2_proofs::poly::commitment::{CommitmentScheme, ParamsProver, Prover, Verifier};
use halo2_proofs::poly::VerificationStrategy;
use halo2_proofs::transcript::{
    Blake2bRead, Blake2bWrite, Challenge255, EncodedChallenge, TranscriptReadBuffer,
    TranscriptWriterBuffer,
};

use halo2curves::bn256::Fr;
use halo2curves::ff::{FromUniformBytes, WithSmallOrderMulGroup};
use rand_core::{OsRng, RngCore, SeedableRng};
use std::marker::PhantomData;

use halo2_proofs::circuit::AssignedCell;
use halo2_proofs::circuit::Chip;
use rand_chacha::ChaCha20Rng;

use halo2curves::ff::Field;
use poseidon_base::primitives::ConstantLength;
use poseidon_base::primitives::P128Pow5T3;
use poseidon_base::primitives::P128Pow5T3Compact;
use poseidon_circuit::poseidon::Hash;
use poseidon_circuit::poseidon::Pow5Chip;
use poseidon_circuit::poseidon::Pow5Config;

trait LoadingInstructions<F: PrimeField>: Chip<F> {
    type Num;

    fn load_witness(&self, layouter: impl Layouter<F>, x: Value<F>) -> Result<Self::Num, Error>;
    fn load_nonce(&self, layouter: impl Layouter<F>, nonce: Value<F>) -> Result<Self::Num, Error>;
    fn load_constant(&self, layouter: impl Layouter<F>, constant: F) -> Result<Self::Num, Error>;

    fn expose_public(
        &self,
        layouter: impl Layouter<F>,
        num: Self::Num,
        row: usize,
    ) -> Result<(), Error>;
}

struct InputChip<F: PrimeField> {
    config: InputConfig,
    _marker: PhantomData<F>,
}

#[derive(Clone, Debug)]
#[allow(dead_code)]
struct InputConfig {
    witness: Column<Advice>,
    digest: Column<Instance>,
    constant: Column<Fixed>,
}

impl<F: PrimeField> InputChip<F> {
    fn construct(config: <Self as Chip<F>>::Config) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    fn configure(
        meta: &mut ConstraintSystem<F>,
        witness: Column<Advice>,
        digest: Column<Instance>,
        constant: Column<Fixed>,
    ) -> <Self as Chip<F>>::Config {
        meta.enable_equality(witness);
        meta.enable_equality(digest);
        meta.enable_equality(constant);

        InputConfig {
            witness,
            digest,
            constant,
        }
    }
}
// ANCHOR_END: chip-config

// ANCHOR: chip-impl
impl<F: PrimeField> Chip<F> for InputChip<F> {
    type Config = InputConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

#[derive(Clone)]
struct Number<F: PrimeField>(AssignedCell<F, F>);

impl<F: PrimeField> LoadingInstructions<F> for InputChip<F> {
    type Num = Number<F>;

    fn load_witness(
        &self,
        mut layouter: impl Layouter<F>,
        x: Value<F>,
    ) -> Result<Self::Num, Error> {
        let config = self.config();
        layouter.assign_region(
            || "load witness",
            |mut region| {
                region
                    .assign_advice(|| "witness value", config.witness, 0, || x)
                    .map(Number)
            },
        )
    }

    fn load_nonce(
        &self,
        mut layouter: impl Layouter<F>,
        nonce: Value<F>,
    ) -> Result<Self::Num, Error> {
        let config = self.config();
        layouter.assign_region(
            || "load nonce",
            |mut region| {
                region
                    .assign_advice(|| "nonce value", config.witness, 0, || nonce)
                    .map(Number)
            },
        )
    }

    fn load_constant(
        &self,
        mut layouter: impl Layouter<F>,
        constant: F,
    ) -> Result<Self::Num, Error> {
        let config = self.config();

        layouter.assign_region(
            || "load constant",
            |mut region| {
                region
                    .assign_advice_from_constant(|| "constant value", config.witness, 0, constant)
                    .map(Number)
            },
        )
    }

    fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        num: Self::Num,
        row: usize,
    ) -> Result<(), Error> {
        let config = self.config();
        layouter.constrain_instance(num.0.cell(), config.digest, row)
    }
}

#[derive(Default, Clone)]
struct MyCircuit {
    witness: Value<Fr>,
    nonce: Value<Fr>,
}

const WIDTH: usize = 3;
const RATE: usize = 2;

#[derive(Clone, Debug)]
struct MyCircuitConfig {
    input_config: InputConfig,
    hash_config: Pow5Config<Fr, WIDTH, RATE>,
    commitment_hash_config: Pow5Config<Fr, WIDTH, RATE>,
}

impl Circuit<Fr> for MyCircuit {
    type Config = MyCircuitConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        // LOAD CONFIG

        let witness = meta.advice_column();
        let instance = meta.instance_column();
        let constant = meta.fixed_column();

        let input_config = InputChip::configure(meta, witness, instance, constant);

        let witness_state = (0..WIDTH).map(|_| meta.advice_column()).collect::<Vec<_>>();
        let witness_partial_sbox = meta.advice_column();

        let witness_rc_a = (0..WIDTH).map(|_| meta.fixed_column()).collect::<Vec<_>>();
        let witness_rc_b = (0..WIDTH).map(|_| meta.fixed_column()).collect::<Vec<_>>();

        meta.enable_constant(witness_rc_b[0]);

        let witness_hash_config = Pow5Chip::configure::<P128Pow5T3<Fr>>(
            meta,
            witness_state.try_into().unwrap(),
            witness_partial_sbox,
            witness_rc_a.try_into().unwrap(),
            witness_rc_b.try_into().unwrap(),
        );

        // POSEIDON CONFIG

        let state = (0..WIDTH).map(|_| meta.advice_column()).collect::<Vec<_>>();
        let partial_sbox = meta.advice_column();

        let rc_a = (0..WIDTH).map(|_| meta.fixed_column()).collect::<Vec<_>>();
        let rc_b = (0..WIDTH).map(|_| meta.fixed_column()).collect::<Vec<_>>();

        meta.enable_constant(rc_b[0]);

        let hash_config = Pow5Chip::configure::<P128Pow5T3<Fr>>(
            meta,
            state.try_into().unwrap(),
            partial_sbox,
            rc_a.try_into().unwrap(),
            rc_b.try_into().unwrap(),
        );

        return Self::Config {
            input_config,
            hash_config,
            commitment_hash_config: witness_hash_config,
        };
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {
        let input_chip = InputChip::<_>::construct(config.input_config);

        let x = input_chip.load_witness(layouter.namespace(|| "load secret"), self.witness)?;
        let nonce = input_chip.load_nonce(layouter.namespace(|| "load nonce"), self.nonce)?;
        let c = input_chip.load_constant(layouter.namespace(|| "load const"), Fr::from(0u64))?;

        let commitment_hash_chip = Pow5Chip::construct(config.commitment_hash_config.clone());
        let commitment_hasher = Hash::<_, _, P128Pow5T3<Fr>, ConstantLength<2>, WIDTH, RATE>::init(
            commitment_hash_chip,
            layouter.namespace(|| "init witness"),
        )?;

        let commitment_digest =
            commitment_hasher.hash(layouter.namespace(|| "commitment"), [x.0.clone(), c.0])?;
        input_chip.expose_public(
            layouter.namespace(|| "expose commitment"),
            Number(commitment_digest),
            1,
        )?;

        // START HASHING
        let poseidon_chip = Pow5Chip::construct(config.hash_config.clone());
        let hasher = Hash::<_, _, P128Pow5T3<Fr>, ConstantLength<2>, WIDTH, RATE>::init(
            poseidon_chip,
            layouter.namespace(|| "init"),
        )?;

        let nullifier = hasher.hash(layouter.namespace(|| "hash"), [x.0, nonce.0])?;
        input_chip.expose_public(
            layouter.namespace(|| "expose nullifier"),
            Number(nullifier),
            0,
        )?;

        Ok(())
    }
}

const K: u32 = 6;

pub fn keygen<Scheme: CommitmentScheme<Scalar = halo2curves::bn256::Fr>>(
    params: &Scheme::ParamsProver,
) -> ProvingKey<Scheme::Curve>
where
    Scheme::Scalar: FromUniformBytes<64> + WithSmallOrderMulGroup<3>,
{
    let empty_circuit = MyCircuit {
        witness: Value::unknown(),
        nonce: Value::unknown(),
    };

    let vk = keygen_vk(params, &empty_circuit).expect("keygen_vk should not fail");
    let pk = keygen_pk(params, vk, &empty_circuit).expect("keygen_pk should not fail");

    pk
}

pub fn create_proof<
    'params,
    Scheme: CommitmentScheme<Scalar = halo2curves::bn256::Fr>,
    P: Prover<'params, Scheme>,
    E: EncodedChallenge<Scheme::Curve>,
    R: RngCore,
    T: TranscriptWriterBuffer<Vec<u8>, Scheme::Curve, E>,
>(
    rng: R,
    params: &'params Scheme::ParamsProver,
    pk: &ProvingKey<Scheme::Curve>,
) -> (Vec<u8>, Fr, Fr)
where
    Scheme::Scalar: Ord + WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
{
    let n_rng = OsRng;
    let witness = Fr::from_str_vartime(
        "0", /* This is just an example of how to create a proof, no luck finding it here! */
    )
    .unwrap();
    let nonce = Fr::random(n_rng);

    let msg = [witness, nonce];
    let nullifier = poseidon_base::primitives::Hash::<
        _,
        P128Pow5T3Compact<Fr>,
        ConstantLength<2>,
        WIDTH,
        RATE,
    >::init()
    .hash(msg);

    let msg = [witness, Fr::from(0u64)];
    let commitment = poseidon_base::primitives::Hash::<
        _,
        P128Pow5T3Compact<Fr>,
        ConstantLength<2>,
        WIDTH,
        RATE,
    >::init()
    .hash(msg);

    let circuit = MyCircuit {
        witness: Value::known(witness),
        nonce: Value::known(nonce),
    };

    let public_inputs = vec![nullifier, commitment];
    let mut transcript = T::init(vec![]);

    create_plonk_proof::<Scheme, P, _, _, _, _>(
        params,
        pk,
        &[circuit],
        &[&[&public_inputs.clone()]],
        rng,
        &mut transcript,
    )
    .expect("proof generation should not fail");

    (transcript.finalize(), nullifier, commitment)
}

pub fn verify_proof<
    'a,
    'params,
    Scheme: CommitmentScheme<Scalar = halo2curves::bn256::Fr>,
    V: Verifier<'params, Scheme>,
    E: EncodedChallenge<Scheme::Curve>,
    T: TranscriptReadBuffer<&'a [u8], Scheme::Curve, E>,
    Strategy: VerificationStrategy<'params, Scheme, V, Output = Strategy>,
>(
    params_verifier: &'params Scheme::ParamsVerifier,
    vk: &VerifyingKey<Scheme::Curve>,
    proof: &'a [u8],
    nullifier: Fr,
    commitment: Fr,
) where
    Scheme::Scalar: Ord + WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
{
    let pubinputs = vec![nullifier, commitment];

    let mut transcript = T::init(proof);

    let strategy = Strategy::new(params_verifier);
    let strategy = verify_plonk_proof(
        params_verifier,
        vk,
        strategy,
        &[&[&pubinputs[..]]],
        &mut transcript,
    )
    .unwrap();

    assert!(strategy.finalize());
}

pub fn shplonk() -> (Vec<u8>, Fr, Fr) {
    use halo2_proofs::poly::kzg::commitment::{KZGCommitmentScheme, ParamsKZG};
    use halo2_proofs::poly::kzg::multiopen::{ProverSHPLONK, VerifierSHPLONK};
    use halo2_proofs::poly::kzg::strategy::AccumulatorStrategy;
    use halo2curves::bn256::Bn256;
    use rand_chacha::ChaCha20Rng;
    use rand_core::SeedableRng;

    let setup_rng = ChaCha20Rng::from_seed([1u8; 32]);
    let params = ParamsKZG::<Bn256>::setup(K, setup_rng);
    let rng = OsRng;

    let pk = keygen::<KZGCommitmentScheme<_>>(&params);

    let (proof, nullifier, commitment) =
        create_proof::<_, ProverSHPLONK<_>, _, _, Blake2bWrite<_, _, Challenge255<_>>>(
            rng, &params, &pk,
        );

    let verifier_params = params.verifier_params();

    verify_proof::<
        _,
        VerifierSHPLONK<_>,
        _,
        Blake2bRead<_, _, Challenge255<_>>,
        AccumulatorStrategy<_>,
    >(
        verifier_params,
        pk.get_vk(),
        &proof[..],
        nullifier,
        commitment,
    );

    (proof, nullifier, commitment)
}

fn from_serialized(i: usize) -> (Vec<u8>, Fr, Fr) {
    use halo2_proofs::poly::kzg::commitment::{KZGCommitmentScheme, ParamsKZG};
    use halo2_proofs::poly::kzg::multiopen::VerifierSHPLONK;
    use halo2_proofs::poly::kzg::strategy::AccumulatorStrategy;
    use halo2curves::bn256::Bn256;

    let setup_rng = ChaCha20Rng::from_seed([1u8; 32]);
    let params = ParamsKZG::<Bn256>::setup(K, setup_rng);

    let pk = keygen::<KZGCommitmentScheme<_>>(&params);

    let (proofs, nullifiers, commitments) = deserialize();

    let proof = proofs[i].clone();
    let nullifier = nullifiers[i];
    let commitment = commitments[i];

    let verifier_params = params.verifier_params();
    verify_proof::<
        _,
        VerifierSHPLONK<_>,
        _,
        Blake2bRead<_, _, Challenge255<_>>,
        AccumulatorStrategy<_>,
    >(
        verifier_params,
        pk.get_vk(),
        &proof[..],
        nullifier,
        commitment,
    );

    (proof, nullifier, commitment)
}

use std::fs::File;
use std::io::Write;

pub fn serialize() {
    for i in 0..64 {
        let (proof, nullifier, commitment) = shplonk();

        let filename = format!("./proofs/proof_{}.bin", i);
        let mut file = File::create(&filename).unwrap();
        file.write_all(&proof).unwrap();

        let filename = format!("./nullifiers/nullifier_{}.bin", i);
        let mut file = File::create(&filename).unwrap();
        file.write_all(&nullifier.to_repr()).unwrap();

        let filename = format!("./commitments/commitment_{}.bin", i);
        let mut file = File::create(&filename).unwrap();
        file.write_all(&commitment.to_repr()).unwrap();
    }
}

pub fn deserialize() -> (Vec<Vec<u8>>, Vec<Fr>, Vec<Fr>) {
    use std::fs::File;
    use std::io::Read;

    let mut proofs: Vec<Vec<u8>> = Vec::<_>::new();
    let mut nullifiers: Vec<Fr> = Vec::<_>::new();
    let mut commitments: Vec<Fr> = Vec::<_>::new();

    for i in 0..64 {
        let filename = format!("./proofs/proof_{}.bin", i);
        let mut file = File::open(&filename).unwrap();
        let mut proof = Vec::new();
        file.read_to_end(&mut proof).unwrap();
        proofs.push(proof);

        // serialize digests
        let filename = format!("./nullifiers/nullifier_{}.bin", i);
        let mut file = File::open(&filename).unwrap();
        let mut nullifier_bytes: Vec<u8> = Vec::new();
        file.read_to_end(&mut nullifier_bytes).unwrap();

        let nullifier: Fr = Fr::from_repr(nullifier_bytes.try_into().unwrap()).unwrap();

        let filename = format!("./commitments/commitment_{}.bin", i);
        let mut file = File::open(&filename).unwrap();
        let mut cm_bytes: Vec<u8> = Vec::new();
        file.read_to_end(&mut cm_bytes).unwrap();

        let commitment: Fr = Fr::from_repr(cm_bytes.try_into().unwrap()).unwrap();

        nullifiers.push(nullifier);
        commitments.push(commitment);
    }

    (proofs, nullifiers, commitments)
}

pub fn main() {
    welcome();
    puzzle(PUZZLE_DESCRIPTION);

    /* This is how the serialized proofs, nullifiers and commitments were created. */
    // serialize();
    {
        use halo2_proofs::poly::kzg::commitment::{KZGCommitmentScheme, ParamsKZG};
        use halo2_proofs::poly::kzg::multiopen::VerifierSHPLONK;
        use halo2_proofs::poly::kzg::strategy::AccumulatorStrategy;
        use halo2curves::bn256::Bn256;
        use rand_chacha::ChaCha20Rng;
        use rand_core::SeedableRng;

        pub fn extract_info_from_proof<
            'a,
            'params,
            Scheme: CommitmentScheme<Scalar = halo2curves::bn256::Fr>,
            V: Verifier<'params, Scheme>,
            E: EncodedChallenge<Scheme::Curve>,
            T: TranscriptReadBuffer<&'a [u8], Scheme::Curve, E>,
            Strategy: VerificationStrategy<'params, Scheme, V, Output = Strategy>,
        >(
            params_verifier: &'params Scheme::ParamsVerifier,
            vk: &VerifyingKey<Scheme::Curve>,
            proof: &'a [u8],
            nullifier: Fr,
            commitment: Fr,
        ) -> (Fr, Fr)
        where
            Scheme::Scalar: Ord + WithSmallOrderMulGroup<3> + FromUniformBytes<64>,
        {
            let pubinputs = vec![nullifier, commitment];

            let mut transcript = T::init(proof);

            let strategy = Strategy::new(params_verifier);
            halo2_proofs::plonk::verifier::extract_info_from_proof(
                params_verifier,
                vk,
                strategy,
                &[&[&pubinputs[..]]],
                &mut transcript,
            )
            .unwrap()
        }

        let setup_rng = ChaCha20Rng::from_seed([1u8; 32]);
        let params = ParamsKZG::<Bn256>::setup(K, setup_rng);
        let pk = keygen::<KZGCommitmentScheme<_>>(&params);
        let verifier_params = params.verifier_params();

        // Extract the evaluations of advice[0].advice_polys[1]
        let mut extracted_evals = Vec::new();
        for i in 0..64 {
            let (proof, nullifier, commitment) = from_serialized(i);

            let (x, eval_at_x) =
                extract_info_from_proof::<
                    _,
                    VerifierSHPLONK<_>,
                    _,
                    Blake2bRead<_, _, Challenge255<_>>,
                    AccumulatorStrategy<_>,
                >(verifier_params, pk.get_vk(), &proof, nullifier, commitment);
            println!("extracted[{i}]: x = {x:?}, e = {eval_at_x:?}");
            extracted_evals.push((x, eval_at_x))
        }

        // Interpolate the polynomial at omega^2
        let omega2 = pk.get_vk().get_domain().get_omega().square();
        let mut secret = Fr::zero();
        for i in 0..64 {
            let mut term = extracted_evals[i].1;
            for j in 0..64 {
                if i != j {
                    term *= omega2 - extracted_evals[j].0;
                    term *= (extracted_evals[i].0 - extracted_evals[j].0)
                        .invert()
                        .unwrap();
                }
            }
            secret += term;
        }
        println!("secret = {secret:?}");

        // Try to debug proof creation
    }

    /* Implement your attack here, to find the index of the encrypted message */

    let secret = Fr::from_str_vartime(
        "2902393715628053125157988380733315934099850103804946746061390165677120635277",
    )
    .unwrap();
    let secret_commitment = poseidon_base::primitives::Hash::<
        _,
        P128Pow5T3Compact<Fr>,
        ConstantLength<2>,
        WIDTH,
        RATE,
    >::init()
    .hash([secret, Fr::from(0u64)]);
    for i in 0..64 {
        let (_, _, commitment) = from_serialized(i);
        assert_eq!(secret_commitment, commitment);
    }
    /* End of attack */
}

const PUZZLE_DESCRIPTION: &str = r"
A few years ago, Bob signed up to SuperCoolAirdrop™.
The process was simple: provide a hash of your private key to register and when your airdrop is ready you'll receive a notification.
Today, Bob finally received a notification from SuperCoolAirdrop™. It's time to claim his airdrop!

The process is simple, he just needs to give a proof of knowledge that he knows the private key associated with the commitment he made years ago.
To prevent replay attacks, SuperCoolAirdrop™ implemented a nullifier system: on top of proving knowledge of the private key, users must create a secret nonce and produce a public nullifier.
Once the SuperCoolAirdrop™ server verifies the proof and logs the nullifier, the proof cannot be re-used.

So Bob picks a random nonce, his favorite proof system and sends in a proof. The proof gets rejected... weird. He samples a new nonce and tries again. And again. And again. Still, his proofs get rejected.

Suddenly it dawns on him. Is SuperCoolAirdrop™ legit? Is this an attempt to steal his private key?
";
