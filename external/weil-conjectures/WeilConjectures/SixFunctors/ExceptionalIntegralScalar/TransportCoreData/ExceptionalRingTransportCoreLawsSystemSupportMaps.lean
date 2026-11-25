/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.ExceptionalRingTransportCoreLawsSystemSupportObjects
public import WeilConjectures.CategoryTheory.SixFunctors.FunctorObjectConjugation

/-! Map part of the exceptional transport support identity.
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Propositions 5.24,
5.26 (blueprint: lem-sf-exceptional-ring-transport-core-system-support-law-maps).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients

section Conjugation

variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)
  (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
  (left : ∀ s : RingStage.{u} l, LeftRealization.{u} l Ω c s (operation s))
  (d : TransportCoreData l Ω D hl c operation left)
  (α : ∀ (E : FieldStage.{u} l) (K : (sequenceProperty l E X).FullSubcategory),
    (d.F E).obj K ≅ (d.F E).obj K)

end Conjugation

/- STATEMENT-DISPUTED: `TransportCoreData.F` is an arbitrary functor supplied with
comparison isomorphisms, not a prescribed strict lift of the support composite.
`TransportCoreData.conjugateSystemF` preserves every required data field while
conjugating its maps by arbitrary object automorphisms. Whenever a family changes
a map, `not_forall_system_support_map_of_conjugation` refutes the universal claim.
The object comparison alone cannot supply this missing normalization. -/

/--
The strict-system support comparison on morphisms at one fixed field stage.
Together with the object component, this is the map premise of `Functor.ext`.
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Propositions 5.24,
5.26 (blueprint: lem-sf-exceptional-ring-transport-core-system-support-law-maps).
-/
theorem exceptional_transport_core_system_support_map
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (operation : ∀ s : RingStage.{u} l, Operation.{u} l Ω X Y (s.stage l))
    (left : ∀ s : RingStage.{u} l,
      LeftRealization.{u} l Ω c s (operation s))
    (d : TransportCoreData l Ω D hl c operation left)
    (E : FieldStage.{u} l)
    {K K' : (sequenceProperty l E X).FullSubcategory} (u : K ⟶ K') :
    (d.F E ⋙ (sequenceProperty l E Y).ι).map u =
      eqToHom (exceptional_transport_core_system_support_obj
        l Ω D hl f c operation left d E K) ≫
      ((sequenceProperty l E X).ι ⋙
        IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i ⋙
          IntegralSystemRealization.Operations.push l E.carrier (d.operations E) c.g).map u ≫
      eqToHom (exceptional_transport_core_system_support_obj
        l Ω D hl f c operation left d E K').symm := by
  sorry

end WeilConjectures.ExceptionalIntegralScalar
