/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.SixFunctors.Normalized.NormalizedDVRAdicConeModel

/-! # Finite reductions of a normalized DVR Roos limit -/

@[expose] public noncomputable section
set_option autoImplicit false
universe d t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})
  (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
/-- The canonical standard derived category, registered only in this file. -/
abbrev normalizedDVRRoosFiniteReductionLocal1 :
    HasDerivedCategory (completedIntegralModuleSheaves l E X D hl) :=
  HasDerivedCategory.standard _
attribute [local instance] normalizedDVRRoosFiniteReductionLocal1
/-- Canonical abelian sheafification, registered only in this file. -/
abbrev normalizedDVRRoosFiniteReductionLocal3 :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
    AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} X
attribute [local instance] normalizedDVRRoosFiniteReductionLocal3
/-- The canonical locally bijective sheafification criterion, registered locally. -/
abbrev normalizedDVRRoosFiniteReductionLocal4 :
    (AlgebraicGeometry.Scheme.ProEt.topology X).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} X
attribute [local instance] normalizedDVRRoosFiniteReductionLocal4

private theorem exactDerived_reflects_iso
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [F.Faithful]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {K L : DerivedCategory A} (f : K ⟶ L) (hf : IsIso (F.mapDerivedCategory.map f)) :
    IsIso f := by
  have := hf
  rw [DerivedCategory.isIso_iff]
  intro i
  have hm : IsIso (F.map ((DerivedCategory.homologyFunctor A i).map f)) :=
    (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso i) f).mpr
      (by dsimp only [Functor.comp_map]; infer_instance)
  have := hm
  have : Mono ((DerivedCategory.homologyFunctor A i).map f) :=
    F.mono_of_mono_map inferInstance
  have : Epi ((DerivedCategory.homologyFunctor A i).map f) := F.epi_of_epi_map inferInstance
  exact isIso_of_mono_of_epi _

/-- Finite reduction of the Roos limit of a normalized DVR tower.
Source: blueprint lemma-sp-tower-adjunction-foundation--2, proof paragraphs 1--4;
Bhatt--Scholze, Lemmas 3.5.4--3.5.7.
(blueprint: lem-coef-normalized-dvr-roos-finite-reduction).

Proof: strictify the finite-coefficient complexes with K-flat resolutions with flat
terms, representing each successor map by a roof before resolving its source. The
level identifications and their products transport the given Roos triangle to the
strict model, preserving projections. Fix exponent n+1 and remove its finite prefix.
The two-term free completed-coefficient resolution of the finite quotient commutes
with products and the Roos cone. Its tensor with the strict tower maps to the
constant n-th finite complex, with fiber the shifted reduced complex and transitions
multiplied by the corresponding uniformizer power. Every n+1 successive fiber
transitions vanish. The inverse of 1-s on its product is the finite geometric sum,
so its Roos limit vanishes. Taking limits gives the finite comparison isomorphism.
The tensor unit formula identifies it with the adjoint of the specified projection.
Exact restriction detects isomorphisms, since it preserves the underlying abelian
sheaf. Changing the tensor-restriction adjunction conjugates this comparison by an
isomorphism, so any adjunction between the fixed functors gives an invertible map.
The argument includes n=0 (exponent one), zero towers and the empty scheme and
uses no bounds or constructibility. -/
theorem normalizedDVRRoos_finite_reduction
    (T : NormalizedDVRTower l E X D hl)
    (M : completedIntegralDerivedCategory l E X D hl)
    [HasProduct (fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower)]
    (p : M ⟶ ∏ᶜ fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower)
    (δ : (∏ᶜ fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower) ⟶
      M⟦(1 : ℤ)⟧)
    (hc : IsDerivedLimitTriangle
      (fun n : ℕ ↦ (normalizedDVRTowerTransition l E X D hl n.le_succ).app T.tower)
      M p δ) (n : ℕ)
    (adj : scalarReductionDerivedExtension l E X n ⊣
      scalarReductionDerivedRestriction l E X n) :
    IsIso ((adj.homEquiv M (T.M n)).symm
      (p ≫ Pi.π _ n ≫ (T.evaluationIso n).hom)) := by
  obtain ⟨S, hS, hlin, hprod, ϖ, U, hU, eU, _, c, hc, a, he⟩ :=
    normalizedDVR_adic_cone_model l E X D hl T M p δ hc n adj
  let := hS
  let := hlin
  let := hprod
  have hi := hU.isIso_π_comp (n + 1) hc
  have hm : IsIso ((scalarReductionDerivedRestriction l E X n).map
      ((adj.homEquiv M (T.M n)).symm
        (p ≫ Pi.π _ n ≫ (T.evaluationIso n).hom))) := by
    rw [he]
    simpa only [Category.assoc] using
      (IsIso.comp_isIso' (IsIso.comp_isIso' (inferInstance : IsIso a.hom) hi)
        (IsIso.comp_isIso' (inferInstance : IsIso (eU n).hom)
          (inferInstance : IsIso (T.evaluationIso n).hom)))
  have : (scalarReductionRestriction l E X n).Faithful := ⟨by
      intro K L f g h
      ext U x
      exact congrArg (fun k ↦ (k.val.app U) x) h⟩
  let := scalarReductionRestrictionLimits l E X n
  let := scalarReductionRestrictionColimits l E X n
  exact exactDerived_reflects_iso (scalarReductionRestriction l E X n) _ hm

end WeilConjectures
