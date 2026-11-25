# Checking complete Lean declaration types

A theorem can prove every intended instance while its unapplied constant has
a different order of outer parameters from the target declaration. An example
that supplies arguments, including named implicit arguments, can hide this
difference. A direct assignment of the unapplied constant checks the entire
function type.

This distinction was reproduced with Lean 4.34.0, commit
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`. This is a development technique,
not a replacement for a formal check against the exact target statement or for
an independent reading of what the statement says.

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
The corrected closing theorems are in the Library under
`Langlands/Representation/Smooth/Contragredient/`:
`smoothDualCompactFixedDuality` (`CompactDualityProof.lean`),
`smoothContragredientShortExact` (`ExactProof.lean`) and
`smoothContragredientHomDuality` (`HomDualityProof.lean`), each with the
topology before the module parameters and each module's instances next to
its carrier.

The checks were made against the Library's target statements, on proof
files outside the Library. Passing such a check does not by itself put a
proof or its dependencies into the Library. This note records a
reproducible checking lesson; it establishes no local Langlands result.

The compact-duality correction was also confirmed independently, in a
separate proof of that statement.
