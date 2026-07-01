# LeanDY: Type-Based and Trace-Based Symbolic Protocol Verification in Lean

LeanDY is a Lean 4 library for symbolic protocol verification. It combines compositional type-based reasoning with trace-based proofs, enabling modular verification of stateful and unbounded protocols against a Dolev-Yao adversary. The library provides a DSL for protocol specifications, a type system for semi-automatic verification of confidentiality and well-formedness, and supports conditional secrecy properties for protocols using XOR.

## Library Structure

```
LeanDY/
├── Leandy/                      # Library
│   ├── Core/                    # Core type system, symbolic bytes, traces
│   ├── Generalities/            # General utility lemmas
│   ├── Lib/                     # High-Level abstractions and protocol DSL
│   └── Macros/                  # Custom tactics and automation
└── Protocols/                   # Protocol formalizations and examples
```

## Protocol Formalizations

The library includes formalizations of several example protocols:

- **SimpleAuth**: Simple authentication protocol example
- **DistributedOTP**: One-time password using XOR
- **OneHop**: Basic single-hop payment protocol
- **MultiHop**: Multi-hop atomic payment protocol (example of a conditional release chain protocol with XOR)

### Payment Channels

The `PaymentChannel` protocol formalizes a two-party payment channel on top of a SegWit-style UTXO blockchain model. It captures:
- **Channel opening**: Funding transaction with 2-of-2 multisig and initial commitment exchange
- **Off-chain updates**: Unbounded sequence of balance updates via revocation-based commitments
- **Revocation mechanism**: Each update reveals secrets that enable punishment of outdated states
- **Punishment transactions**: If a revoked state is published on-chain, the counterparty can claim all funds

## Building

```bash
# Download the mathlib build cache
lake exec cache get

# Build the library
lake build

# Build specific protocol proofs
lake build Protocols.SimpleAuth
lake build Protocols.PaymentChannel
```

