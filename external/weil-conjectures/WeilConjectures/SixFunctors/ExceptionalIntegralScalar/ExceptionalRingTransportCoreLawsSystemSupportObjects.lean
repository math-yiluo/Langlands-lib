/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralScalar.TransportCoreData.ExceptionalRingTransportCoreData
import WeilConjectures.AlgebraicGeometry.Finite.FiniteCtfTriangulated

/-! Object part of the exceptional transport support identity.
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Propositions 5.24,
5.26 (blueprint: lem-sf-exceptional-ring-transport-core-system-support-law-objects).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients

private theorem normalizedCoefficientSequence_of_iso
    (l : ℕ) [Fact l.Prime] (E : FieldStage.{u} l) (T : Scheme.{u})
    {M N : coefficientSequenceDerived l E.carrier T} (e : M ≅ N)
    (hM : IsNormalizedCoefficientSequence l E.carrier T M) :
    IsNormalizedCoefficientSequence l E.carrier T N := by
  intro m n h P
  let a := (coefficientSequenceDerivedEvaluation l E.carrier T n).mapIso e
  let b := (coefficientSequenceDerivedEvaluation l E.carrier T m).mapIso e
  have comm (f : (coefficientSequenceDerivedEvaluation l E.carrier T n).obj N ⟶ P) :
      (coefficientSequenceDerivedTransition l E.carrier T h).app M ≫
          (normalizedDVRRes l E.carrier T h).map (a.hom ≫ f) =
        b.hom ≫ (coefficientSequenceDerivedTransition l E.carrier T h).app N ≫
          (normalizedDVRRes l E.carrier T h).map f := by
    rw [Functor.map_comp, ← Category.assoc]
    simpa only [a, b, Functor.comp_map, Functor.mapIso_hom, Category.assoc] using
      congrArg (fun t ↦ t ≫ (normalizedDVRRes l E.carrier T h).map f)
        ((coefficientSequenceDerivedTransition l E.carrier T h).naturality e.hom).symm
  constructor
  · intro f g hfg
    apply (cancel_epi a.hom).1
    apply (hM h P).1
    dsimp only at hfg ⊢
    rw [comm, comm, hfg]
  · intro g
    obtain ⟨f, hf⟩ := (hM h P).2 (b.hom ≫ g)
    refine ⟨a.inv ≫ f, ?_⟩
    apply (cancel_epi b.hom).1
    rw [← comm]
    simpa only [Iso.hom_inv_id_assoc] using hf

section SupportNormalization

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

include d

end SupportNormalization

/- STATEMENT-DISPUTED: `TransportCoreData.F` is an arbitrary representative, related
by isomorphisms to the integral operations. Isomorphisms do not imply equality of
objects. `TransportCoreData.rebaseF` preserves all the data-field types while
changing that representative. `not_forall_system_support_obj_of_iso` proves the
resulting obstruction whenever the underlying outputs differ. For the constructed
strict lift, `TransportCoreData.normalizeSupport_support` proves the full support
identity from an ambient comparison, deriving preservation from it. The current
hypotheses do not specify that lift or its object representatives. -/

/--
The strict-system support comparison on objects at one fixed field stage.
It is the object component used with the corresponding map component to
assemble the support functor equality.
Source: Zheng, Constructions 4.1 and 5.25, Lemma 5.22 and Propositions 5.24,
5.26 (blueprint: lem-sf-exceptional-ring-transport-core-system-support-law-objects).
-/
theorem exceptional_transport_core_system_support_obj
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
    (E : FieldStage.{u} l) (K : (sequenceProperty l E X).FullSubcategory) :
    (d.F E ⋙ (sequenceProperty l E Y).ι).obj K =
      ((sequenceProperty l E X).ι ⋙
        IntegralSystemRealization.Operations.shriek l E.carrier (d.operations E) c.i ⋙
          IntegralSystemRealization.Operations.push l E.carrier (d.operations E) c.g).obj K := by
  sorry

end WeilConjectures.ExceptionalIntegralScalar
