# Checking complete Lean declaration types

A theorem can prove every intended instance while its unapplied constant has
a different order of outer parameters from the target declaration. An example
that supplies arguments, including named implicit arguments, can hide this
difference. A direct assignment of the unapplied constant checks the entire
function type.

Worker 0 reproduced this distinction with Lean 4.34.0, commit
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`. This is a development technique,
not a replacement for the project's formal exact-target check or independent
semantic review.

## Small reproducible example

The following file compiles without diagnostics. Both the applied example and
the complete-declaration example are intentional.

```lean
namespace DeclarationExample

universe u v

def Target (α : Type u) (β : Type v) : Prop :=
  ∀ (x : α) (y : β), x = x ∧ y = y

theorem reversed (β : Type v) (α : Type u) : Target α β := by
  intro x y
  exact ⟨rfl, rfl⟩

example (α : Type u) (β : Type v) : Target α β :=
  reversed β α

theorem ordered (α : Type u) (β : Type v) : Target α β := by
  intro x y
  exact ⟨rfl, rfl⟩

example : ∀ (α : Type u) (β : Type v), Target α β :=
  @ordered

end DeclarationExample
```

In a separate file importing the example, this assignment is expected to fail:

```lean
open DeclarationExample

universe u v

example : ∀ (α : Type u) (β : Type v), Target α β :=
  @reversed
```

The reported type of `reversed` starts with `β`, then `α`. The expected type
starts with `α`, then `β`. Supplying `reversed β α` in the first file adapts the
arguments; assigning `@reversed` directly does not. The two conclusions are
logically equivalent, but the unapplied declaration types are different.
The positive file returned exit 0; the negative file returned exit 1 with this
type mismatch. Neither uses proof holes or additional axioms.

## Applying the check to a project target

Write the complete outer telescope of the published proposition definition,
including its implicit parameters, typeclass instances and separate universe
levels. Assign the closing constant with `@` and no supplied arguments:

```lean
example :
    ∀ {G : Type uG} [Group G] [TopologicalSpace G]
      {V : Type uV} [AddCommGroup V] [Module ℂ V],
      Langlands.SmoothAdmissibleDualityStatement (G := G) (V := V) :=
  @Langlands.smoothAdmissibleDuality
```

This illustration needs the corresponding project imports and universe
declarations. Keep the proposition's internal hypotheses inside that
proposition. Do not introduce them as additional ambient assumptions merely
to make an example elaborate.

To inspect the actual constant, use:

```lean
set_option pp.universes true in
#check @Langlands.smoothAdmissibleDuality
```

If the outer order differs, explicitly declaring the closing theorem's
parameters in the target's order can fix the signature while preserving the
helper lemmas and proof body. Check the resulting constant directly again.
A diagnostic failure alone does not show that the underlying mathematical
argument is false.

## Project cases and limits

This check found three concrete signature problems in the smooth-duality
development:

- The compact-duality closing theorem put the topology after the module
  parameters.
- The short-exact-sequence closing theorem put all complex module instances
  after the three carrier parameters.
- The Hom-duality closing theorem similarly grouped its complex module
  instances after both carriers.

Explicit closing signatures corrected each case without changing its helpers
or proof body. Admissible duality already had the expected outer order.
The corrected drafts are shared in Task 0 draft 35, content key
`8073b791284e358f46e89687ccd994fa236bb3f6cec30d5974d2ba80fe6fdd08`,
under `Langlands/Representation/Smooth/Contragredient/`.

The checks used published targets and explicitly pending proof drafts.
Passing them does not publish those proofs or make pending dependencies
available in the Library. This note records a reproducible checking lesson;
it establishes no local Langlands result.

Worker 0 authored this note and the examples. Worker 48 independently
confirmed the compact-duality correction in its separate proof contribution.
