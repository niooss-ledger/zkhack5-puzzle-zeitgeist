# Zeitgeist
----------------------

This is a copy of <https://github.com/ZK-Hack/puzzle-zeitgeist> with the solution of the puzzle.
A write-up is available on <https://gist.github.com/niooss-ledger/0290f9daa71ac24300cec41ab871f6d1>.

**DO NOT FORK THE REPOSITORY, AS IT WILL MAKE YOUR SOLUTION PUBLIC. INSTEAD, CLONE IT AND ADD A NEW REMOTE TO A PRIVATE REPOSITORY, OR SUBMIT A GIST**

Trying it out
=============

Use `cargo run --release` to see it in action

Submitting a solution
=====================

[Submit a solution](https://form.typeform.com/to/AzdPoMeY)

[Submit a write-up](https://form.typeform.com/to/HM7GwjVp)

Puzzle description
==================

```
    ______ _   __  _   _            _
    |___  /| | / / | | | |          | |
       / / | |/ /  | |_| | __ _  ___| | __
      / /  |    \  |  _  |/ _` |/ __| |/ /
    ./ /___| |\  \ | | | | (_| | (__|   <
    \_____/\_| \_/ \_| |_/\__,_|\___|_|\_\

A few years ago, Bob signed up to SuperCoolAirdrop™.
The process was simple: provide a hash of your private key to register and when your airdrop is ready you'll receive a notification.
Today, Bob finally received a notification from SuperCoolAirdrop™. It's time to claim his airdrop!

The process is simple, he just needs to give a proof of knowledge that he knows the private key associated with the commitment he made years ago.
To prevent replay attacks, SuperCoolAirdrop™ implemented a nullifier system: on top of proving knowledge of the private key, users must create a secret nonce and produce a public nullifier.
Once the SuperCoolAirdrop™ server verifies the proof and logs the nullifier, the proof cannot be re-used.

So Bob picks a random nonce, his favorite proof system and sends in a proof. The proof gets rejected... weird. He samples a new nonce and tries again. And again. And again. Still, his proofs get rejected.

Suddenly it dawns on him. Is SuperCoolAirdrop™ legit? Is this an attempt to steal his private key?
```
