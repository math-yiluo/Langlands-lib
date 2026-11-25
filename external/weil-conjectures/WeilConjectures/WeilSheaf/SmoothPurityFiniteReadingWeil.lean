/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPuritySemilinearReading
public import WeilConjectures.WeilSheaf.SmoothPurityEquivarianceDetection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOriginReadingProof

/-! # Recovering finite equivariant isomorphisms from étale reading -/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory

/-- A fully faithful reading which commutes with the geometric endofunctors reflects
the existence of an isomorphism with the prescribed Weil data. -/
theorem exists_equivariant_iso_of_fullyFaithful_reading
    {C D : Type*} [Category C] [Category D] {G : C ⥤ C} {G' : D ⥤ D}
    (T : C ⥤ D) (hT : T.FullyFaithful) (c : G ⋙ T ≅ T ⋙ G')
    {K L : C} (φK : G.obj K ⟶ K) (φL : G.obj L ⟶ L)
    (h : ∃ e : T.obj K ≅ T.obj L,
      IsWeilEquivariant G' (transportWeilDatum T c φK) (transportWeilDatum T c φL) e.hom) :
    ∃ e : K ≅ L, IsWeilEquivariant G φK φL e.hom := by
  obtain ⟨e, he⟩ := h
  let e' := hT.preimageIso e
  have hm : T.map e'.hom = e.hom := hT.map_preimage e.hom
  refine ⟨e', hT.map_injective ?_⟩
  apply (purity_map_weil_equation_iff T c φK φL e'.hom).mpr
  rw [hm]
  exact he

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
  [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)
  (X : Over (Spec (.of k)))
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- Étale reading of an ambient finite Weil datum, using the actual comparison-site
base change and the finite coefficient equivalence. -/
noncomputable def purityFiniteReadWeilDatum (g : X.left ⟶ X.left)
    {K : Dᵇc(X.left)⟦Profinite.integersModPowRingObj ℓ E n⟧}
    (φ : L((g)^*⟦Profinite.integersModPowRingObj ℓ E n⟧).obj K.obj ⟶ K.obj) :=
  transportWeilDatum (finiteEtaleReading ℓ E n X)
    (purityFiniteEtaleReadingUpperStarIso ℓ E n g)
    (ObjectProperty.homMk (X := (purityBoundedConstructiblePullback _ g).obj K) (Y := K) φ)

set_option linter.unusedSectionVars false in
/-- An equivariant isomorphism on the small étale site lifts to an equivariant
isomorphism of the ambient finite condensed complexes, also for semilinear Frobenius. -/
theorem exists_finite_equivariant_iso_of_etale_reading (g : X.left ⟶ X.left)
    (K L : Dᵇc(X.left)⟦Profinite.integersModPowRingObj ℓ E n⟧)
    (φK : L((g)^*⟦Profinite.integersModPowRingObj ℓ E n⟧).obj K.obj ⟶ K.obj)
    (φL : L((g)^*⟦Profinite.integersModPowRingObj ℓ E n⟧).obj L.obj ⟶ L.obj)
    (hne : ∃ e : (finiteEtaleReading ℓ E n X).obj K ≅ (finiteEtaleReading ℓ E n X).obj L,
      IsWeilEquivariant
        L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) g)
        (purityFiniteReadWeilDatum ℓ E n X g φK)
        (purityFiniteReadWeilDatum ℓ E n X g φL) e.hom) :
    ∃ e : K.obj ≅ L.obj,
      IsWeilEquivariant L((g)^*⟦Profinite.integersModPowRingObj ℓ E n⟧) φK φL e.hom := by
  have h := exists_equivariant_iso_of_fullyFaithful_reading
    (finiteEtaleReading ℓ E n X)
    (finiteEtaleReadingFullyFaithful (etaleOriginReading ℓ E n X))
    (purityFiniteEtaleReadingUpperStarIso ℓ E n g)
    (ObjectProperty.homMk (X := (purityBoundedConstructiblePullback _ g).obj K) (Y := K) φK)
    (ObjectProperty.homMk (X := (purityBoundedConstructiblePullback _ g).obj L) (Y := L) φL)
    hne
  obtain ⟨e, he⟩ := h
  refine ⟨(boundedConstructible _).ι.mapIso e, ?_⟩
  exact congrArg InducedCategory.Hom.hom he

end AlgebraicGeometry.ProEtale.CondensedRing
