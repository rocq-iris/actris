# ACTRIS ROCQ DEVELOPMENT

This is the official Rocq development regarding the [Actris](https://iris-project.org/actris/) line of work.

## Overview

The [actris](./actris) directory contains the [Actris 2.0](https://iris-project.org/pdfs/2022-lmcs-actris2-final.pdf) (extended from [Actris 1.0](https://iris-project.org/pdfs/2020-popl-actris-final.pdf)) framework for language-agnostic binary dependent separation protocols in Iris, along with its instantiation in HeapLang, and the [semantic session type system](https://iris-project.org/pdfs/2021-cpp-sessions-final.pdf) built on top of it.

The [mini_actris](./mini_actris) directory contains [MiniActris](https://apndx.org/pub/mpy9/miniactris.pdf) a first principles approach to Actris based on mutable references in HeapLang.

The [linear_actris](./linear_actris) directory contains [LinearActris](https://iris-project.org/pdfs/2024-popl-dlfactris.pdf), a variant of MiniActris on top of linear Iris, that guarantees deadlock freedom via connectivity graphs.

The [linking_actris](./linking_actris) directory contains [LinkingActris](https://iris-project.org/pdfs/2024-oopsla-linking-actris.pdf), a variant of Actris for HeapLang that permits linking channel endpoints with dual protocols.

The [multris](./multris) directory contains the [Multris](https://iris-project.org/pdfs/2024-oopsla-multris.pdf) framework for language-agnostic multiparty (synchronous) dependent separation protocols in Iris, along with its instantiation in HeapLang.

Actris has additionally been instantiated for [distributed systems](https://github.com/logsem/aneris/tree/master/aneris/examples/reliable_communication), although this instantiation is maintained separately.

## Build and Installation Instructions

Actris can be built in two ways:

- Release version
- Development version

Both versions can be built using opam version 2.5.2, which is available
through most package managers: https://opam.ocaml.org/doc/Install.html

To avoid interference with existing local installations in opam, it is
recommended to first make a new switch with
`opam switch create actris ocaml-base-compiler.5.4.1`

### Installing release version

To install the release version, first add the Rocq release repository:

	opam repo add rocq-released https://rocq-prover.github.io/opam/released/

Then install Actris via:

	opam install rocq-actris

### Building and Installing development version

To install the development version, first add the Iris repository:

	opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git

and then run `make build-dep [num CPU cores]`.

To build all projects run `make -j [num CPU cores]`.

To compile a specific directory, use `./make-package [directory_name] -j [num CPU cores]`.

After compilation, the development version can be installed via `make install`.

## Detailed Insights

### Notation

The following table gives a mapping between the notation in literature
and the Rocq mechanization:

Dependent Separation Protocols:

|        | Papers                        | Rocq mechanization                     |
|--------|-------------------------------|---------------------------------------|
| Send   | `! x_1 .. x_n <v>{ P }. prot` | `<! x_1 .. x_n> MSG v {{ P }}; prot`  |
| Recv   | `? x_1 .. x_n <v>{ P }. prot` | `<? x_1 .. x_n> MSG v {{ P }}; prot`  |
| End    | `end`                         | `END`                                 |
| Select | `prot_1 {Q_1}⊕{Q_2} prot_2`   | `prot_1 <{Q_1}+{Q_2}> prot_2`         |
| Branch | `prot_1 {Q_1}&{Q_2} prot_2`   | `prot_1 <{Q_1}&{Q_2}> prot_2`         |
| Append | `prot_1 · prot_2`             | `prot_1 <++> prot_2`                  |
| Dual   | An overlined protocol         | No notation                           |

Multiparty Dependent Separation Protocols:

|      | Papers                           | Rocq mechanization                             |
|------|----------------------------------|-----------------------------------------------|
| Send | `![i] x_1 .. x_n <v>{ P }. prot` | `<(Send,i) @ x_1 .. x_n> MSG v {{ P }}; prot` |
| Recv | `?[i] x_1 .. x_n <v>{ P }. prot` | `<(Recv,i) @ x_1 .. x_n> MSG v {{ P }}; prot` |
| End  | `end`                            | `END`                                         |
| Dual | An overlined protocol            | No notation                                   |

Semantic Session Types:

|          | Papers                        | Rocq mechanization                     |
|----------|-------------------------------|---------------------------------------|
| Send     | `!_{X_1 .. X_n} A . S`        | `<!! X_1 .. X_n> TY A ; S`            |
| Recv     | `?_{X_1 .. X_n} A . S`        | `<?? X_1 .. X_n> TY A ; S`            |
| End      | `end`                         | `END`                                 |
| Select   | `(+){ Ss }`                   | `lty_choice SEND Ss`                  |
| Branch   | `&{ Ss }`                     | `lty_choice RECV Ss`                  |
| Dual     | An overlined type             | No notation                           |
| N-append | `S^n`                         | lty_napp S n                          |

### Rocq tactics

In order to prove programs using Actris, one can make use of a combination of
[Iris's symbolic execution tactics for HeapLang programs][HeapLang] and
[Actris's symbolic execution tactics for message passing][ActrisProofMode]. The
Actris tactics are as follows:

- `wp_send (t1 .. tn) with "selpat"`: symbolically execute `send c v` by looking
  up ownership of a send protocol `H : c ↣ <!> y1 .. yn, MSG v; {{ P }}; prot`
  in the proof mode context. The tactic instantiates the variables `y1 .. yn`
  using the terms `t1 .. tn` and uses `selpat` to prove `P`. If fewer terms
  `t` are given than variables `y`, they will be instantiated using existential
  variables (evars). The tactic will put `H : c ↣ prot` back into the context.
- `wp_recv (x1 .. xn) as "ipat"`: symbolically execute `recv c` by looking up
  `H : c ↣  <?> y1 .. yn, MSG v; {{ P }}; prot` in the proof mode context. The
  variables `y1 .. yn` are introduced as `x1 .. xn`, and the predicate `P` is
  introduced using the introduction pattern `ipat`. The tactic will put
  `H : c ↣ prot` back into the context.
- `wp_select with "selpat"`: symbolically execute `select c b` by looking up
  `H : c ↣  prot1 {Q1}<+>{Q2} prot2` in the proof mode context. The selection
  pattern `selpat` is used to resolve either `Q1` or `Q2`, based on the chosen
  branch `b`. The tactic will put `H : c ↣  prot1` or `H : c ↣ prot2` back
  into the context based on the chosen branch `b`.
- `wp_branch as ipat1 | ipat2`: symbolically execute `branch c e1 e2` by looking
  up `H : c ↣ prot1 {Q1}<&>{Q2} prot2` in the proof mode context. The result of
  the tactic involves two subgoals, in which `Q1` and `Q2` are introduced using
  the introduction patterns `ipat1` and `ipat2`, respectively. The tactic will
  put `H : c ↣ prot1` and `H : c ↣ prot2` back into the contexts of the two
  respectively goals.

The above tactics implicitly perform normalization of the protocol `prot` in
the hypothesis `H : c ↣ prot`. For example, `wp_send` also works if there is a
channel with the protocol `iProto_dual ((<?> y1 .. yn, MSG v; {{ P }}; END) <++> prot)`.
Concretely, the normalization performs the following actions:

- It re-associates appends (`<++>`), and removes left-identities (`END`) of it.
- It moves appends (`<++>`) into sends (`<!>`), receives (`<?>`), selections
  (`<+>`) and branches (`<&>`).
- It distributes duals (`iProto_dual`) over append (`<++>`).
- It unfolds `prot1` into `prot2` if there is an instance of the type class
  `ProtoUnfold prot1 prot2`. When defining a recursive protocol, it is
  useful to define a `ProtoUnfold` instance to obtain automatic unfolding
  of the recursive protocol. For example, see `sort_protocol_br_unfold` in
  [actris/examples/sort_br_del.v](actris/examples/sort_br_del.v).

Similar proofmode tactics are used all Actris instantiations.
For Multris, additional tactics are included for creating new multiparty channels, and resolving the manual protocol consistency proof obligation.

- `wp_new_chan prots with prots_consistent as (c0 .. cn) "Hc0" .. "Hcn"`:
  symbolically execute `new_chan n` and the subsequent `get_chan 0...n`,
  with the protocols `prot`,  and resolve the protocol consistency obligation via `prots_consistent`.
  The tactic introduces the new channel endpoints as `c0 .. cn` and their
  corresponding endpoint ownership as `Hc0 .. Hcn`.
- `iProto_consistent_take_steps`:
  naively introduces all variables/resources of senders, and eagerly
  instanstiate all variables and resolves resource obligations via IPM framing
  of receivers. If the tactic cannot resolve an obligation by framing it yields
  the remaining proof goal to the user who can manually resolve it.
  If the tactic gets stuck the user can try to reach a new state where progress is possible,
  and reuse the tactic.
  This happens most often when one needs to unfold Rocq definitions, do case analysis on e.g. booleans,
  or use rewrite rules for unfolding recursive definitions.

[HeapLang]: https://gitlab.mpi-sws.org/iris/iris/blob/master/HeapLang.md
[ProofMode]: https://gitlab.mpi-sws.org/iris/iris/blob/master/ProofMode.md
[ActrisProofMode]: actris/channel/proofmode.v

### Theory of Actris

The theory of Actris (semantics of channels, the model, and the proof rules)
can be found in the directory [actris/channel](actris/channel).
The individual types contain the following:

- [actris/channel/proto_model.v](actris/channel/proto_model.v): The
  construction of the model of dependent separation protocols as the solution of
  a recursive domain equation.
- [actris/channel/proto.v](actris/channel/proto.v): The instantiation of
  protocols with the Iris logic, definition of `iProto_own` for channel endpoint
  ownership, and lemmas corresponding to the Actris proof rules.
  The relevant definitions and proof rules are as follows:
  + `iProto Σ`: The type of protocols.
  + `iProto_message`: The constructor for sends and receives.
  + `iProto_end`: The constructor for terminated protocols.
  + `iProto_le`: The subprotocol relation for protocols (notation `⊑`).
- [actris/channel/channel.v](actris/channel/channel.v): The encoding of
  bidirectional channels in terms of Iris's HeapLang language, with specifications
  defined in terms of the dependent separation protocols.
  The relevant definitions and proof rules are as follows:
  + `iProto_pointsto`: endpoint ownership (notation `↣`).
  + `new_chan_spec`, `send_spec` and `recv_spec`: proof rule for `new_chan`,
	`send`, and `recv`.
  + `select_spec` and `branch_spec`: proof rule for the derived (binary)
	`select` and `branch` operations.

### Semantic Session Type System

The logical relation for type safety of a semantic session type system is contained
in the directory [actris/logrel](actris/logrel).
The logical relation is defined across the following files:

- [actris/logrel/model.v](actris/logrel/model.v): Definition of the
  notions of a semantic term type and a semantic session type in terms of
  unary Iris predicates (on values) and Actris protocols, respectively. Also
  provides the required Rocq definitions for creating recursive term/session
  types.
- [actris/logrel/term_types.v](actris/logrel/term_types.v): Definitions
  of the following semantic term types: basic types (integers, booleans, unit),
  sums, products, copyable/affine functions, universally and existentially
  quantified types, unique/shared references, and session-typed channels.
- [actris/logrel/session_types.v](actris/logrel/session_types.v):
  Definitions of the following semantic session types: sending and receiving
  with session polymorphism, n-ary choice. Session type duality is also
  defined here. Recursive session types can be defined using the mechanism
  defined in [actris/logrel/model.v](actris/logrel/model.v).
- [actris/logrel/operators.v](actris/logrel/operators.v):
  Type definitions of unary and binary operators.
- [actris/logrel/contexts.v](actris/logrel/contexts.v):
  Definition of the semantic type contexts, which is used in the semantic
  typing relation. This also contains the rules for updating the context,
  which is used for distributing affine resources across the
  various parts of the proofs inside the typing rules.
- [actris/logrel/term_typing_judgment.v](actris/logrel/term_typing_judgment.v):
  Definition of the semantic typing relation, as well as the proof of type
  soundness, showing that semantically well-typed programs do not get stuck.
- [actris/logrel/subtyping.v](actris/logrel/subtyping.v):
  Definition of the semantic subtyping relation for both term and session types.
  This file also defines the notion of copyability of types in terms of subtyping.
- [actris/logrel/subtyping_rules.v](actris/logrel/subtyping_rules.v):
  Subtyping rules for term types and session types.
- [actris/logrel/term_typing_rules.v](actris/logrel/term_typing_rules.v):
  Semantic typing lemmas (typing rules) for the semantic term types.
- [actris/logrel/session_typing_rules.v](actris/logrel/session_typing_rules.v):
  Semantic typing lemmas (typing rules) for the semantic session types.
- [actris/logrel/napp.v](actris/logrel/napp.v):
  Definition of session types iteratively being appended to themselves a finite
  number of times, with support for swapping e.g. a send over an arbitrary number
  of receives.

An extension to the basic type system is given in
[actris/logrel/lib/mutex.v](actris/logrel/lib/mutex.v), which defines
mutexes as a type-safe abstraction. Mutexes are implemented using spin locks
and allow one to gain exclusive ownership of resources shared between multiple
threads. An encoding of a list type is found in
[actris/logrel/lib/mutex.v](actris/logrel/lib/mutex.v), along with axillary
lemmas, and a weakest precondition for `llength`,
that converts ownership of a list type into a list reference predicate, with
the values of the list made explicit.

## Actris Artifacts

The repository rarely coincide with the final paper artifacts, as these are customised to fit the individual conference artifact evaluation procedure.
Instead, the closest artifact of each paper can be found below:

- [Mixtris: Mechanised Higher-Order Separation Logic for Mixed Choice Multiparty Message Passing](https://doi.org/10.5281/zenodo.18749895)
- [Verified Lock-Free Session Channels with Linking](https://doi.org/10.5281/zenodo.13599952)
- [Multris: Functional Verification of Multiparty Message Passing in Separation Logic](https://dl.acm.org/doi/10.1145/3689762)
- [Deadlock-Free Separation Logic: Linearity Yields Progress for Dependent Higher-Order Message Passing](https://doi.org/10.5281/zenodo.8422755)
- [Verifying Reliable Network Components in a Distributed Separation Logic with Dependent Separation Protocols](https://zenodo.org/records/8121688)
- [Dependent Session Protocols in Separation Logic from First Principles (Functional Pearl)](https://doi.org/10.5281/zenodo.7993904)
- [Actris 2.0](https://gitlab.mpi-sws.org/iris/actris/-/tree/lmcs)
- [Machine-Checked Semantic Session Typing](https://zenodo.org/records/4322752)
- [Actris 1.0](https://dl.acm.org/do/10.1145/3373096/)
