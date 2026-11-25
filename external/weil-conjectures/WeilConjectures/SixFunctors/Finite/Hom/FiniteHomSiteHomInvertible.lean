/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coef.CoefFiniteHomSiteDescentData
import WeilConjectures.AlgebraicGeometry.Finite.FiniteDualitySiteComparison
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonFaithful
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicSiteHomTransport

/-! # A component of finite Hom site descent

Source: blueprint `lem-coef-finite-hom-site-descent`, final site comparison argument.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem siteHom_uncurry
    {A : Type*} [Category A] {H : Aᵒᵖ × A ⥤ A}
    (S : CoefficientClosedStructure H) (T P Q : A) (f : T ⟶ H.obj (op P, Q)) :
    (S.transpose T P Q).symm f =
      S.tensor.map (Prod.mkHom f (𝟙 P)) ≫ S.evaluation P Q := by
  simpa [CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor,
    CoefficientClosedStructure.evaluation] using!
    (S.adjunction P).homEquiv_counit T Q f

private theorem siteHom_uncurry_precomp
    {A : Type*} [Category A] {H : Aᵒᵖ × A ⥤ A}
    (S : CoefficientClosedStructure H) {T T' P Q : A}
    (f : T' ⟶ T) (z : T ⟶ H.obj (op P, Q)) :
    (S.transpose T' P Q).symm (f ≫ z) =
      S.tensor.map (Prod.mkHom f (𝟙 P)) ≫ (S.transpose T P Q).symm z := by
  rw [siteHom_uncurry, siteHom_uncurry]
  have ht : Prod.mkHom (f ≫ z) (𝟙 P) =
      Prod.mkHom f (𝟙 P) ≫ Prod.mkHom z (𝟙 P) := by simp
  rw [ht, S.tensor.map_comp, Category.assoc]

private theorem siteHom_transpose
    {A : Type*} {B : Type*} [Category A] [Category B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor)
    (T P Q : A) (f : SA.tensor.obj (T, P) ⟶ Q) :
    F.map (SA.transpose T P Q f) ≫ coefficientBaseChangeHom SA SB F μ P Q =
      SB.transpose (F.obj T) (F.obj P) (F.obj Q) (μ.inv.app (T, P) ≫ F.map f) := by
  apply (SB.transpose _ _ _).symm.injective
  rw [siteHom_uncurry_precomp, Equiv.symm_apply_apply]
  change SB.tensor.map _ ≫ (SB.transpose _ _ _).symm (SB.transpose _ _ _ _) = _
  rw [Equiv.symm_apply_apply, ← Category.assoc]
  have hn := μ.inv.naturality (Prod.mkHom (SA.transpose T P Q f) (𝟙 P))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  rw [F.map_id] at hn
  rw [hn, Category.assoc, ← F.map_comp, ← siteHom_uncurry, Equiv.symm_apply_apply]

private theorem siteHom_isIso_of_fullyFaithful
    {A : Type*} {B : Type*} [Category A] [Category B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (ff : F.FullyFaithful)
    (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) (K M : A)
    (e : F.obj (HA.obj (op K, M)) ≅ HB.obj (op (F.obj K), F.obj M)) :
    IsIso (coefficientBaseChangeHom SA SB F μ K M) := by
  let T := HA.obj (op K, M)
  let c := coefficientBaseChangeHom SA SB F μ K M
  let h : (F.obj T ⟶ F.obj T) ≃ (F.obj T ⟶ HB.obj (op (F.obj K), F.obj M)) :=
    ff.homEquiv.symm.trans ((SA.transpose T K M).symm.trans
      (ff.homEquiv.trans (((μ.app (T, K)).homCongr (Iso.refl (F.obj M))).trans
        (SB.transpose (F.obj T) (F.obj K) (F.obj M)))))
  have hh (x : F.obj T ⟶ F.obj T) : h x = x ≫ c := by
    obtain ⟨g, rfl⟩ := ff.map_surjective x
    dsimp [h, Functor.FullyFaithful.homEquiv, Iso.homCongr]
    rw [ff.preimage_map, Category.comp_id]
    simpa only [Equiv.apply_symm_apply] using
      (siteHom_transpose SA SB F μ T K M ((SA.transpose T K M).symm g)).symm
  obtain ⟨t, ht⟩ := h.surjective e.hom
  rw [hh] at ht
  have hr : (e.inv ≫ t) ≫ c = 𝟙 _ := by
    rw [Category.assoc, ht, e.inv_hom_id]
  have hl : c ≫ (e.inv ≫ t) = 𝟙 _ := by
    apply h.injective
    rw [hh, hh, Category.assoc, hr, Category.comp_id, Category.id_comp]
  exact ⟨⟨e.inv ≫ t, hl, hr⟩⟩

attribute [local irreducible] coefficientBaseChangeHom finiteHomEtaleClosed
  finiteIntrinsicClosed finiteHomNuTensor

/-- The specified evaluation comparison into the intrinsic category is invertible
on a finite-Tor constructible first input and bounded constructible second input.
Source: blueprint `lem-coef-finite-hom-site-descent`, proof step 5; finite-duality
site comparison (blueprint: lem-coef-finite-hom-site-hom-invertible).

Proof: ordinary finite duality and intrinsicSiteHom_transport give an object
isomorphism from inverse image of the etale Hom to the intrinsic Hom of the two
inverse images. The derived inverse image is fully faithful: apply finite primary
unbounded comparison, compose with the exact realization equivalence, and use the
exact-derived composition isomorphism. For any fully faithful functor with an
invertible tensor comparison, transposition and its Hom bijections identify
postcomposition by the canonical Hom comparison with a bijection on Hom sets
from every object in its image. Test at the inverse image of the etale Hom. The
object isomorphism and surjectivity provide a right inverse to the canonical
comparison; injectivity then gives the left inverse. Thus the actual specified
arrow is invertible, without choosing an evaluation-normalized presentation
isomorphism. The second input only requires bounded constructibility. -/
theorem finiteHomSiteHomInvertible
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] :
    ∀ (n : ℕ) (K M : finiteHomEtale l E X n),
      finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X K →
      coefFiniteHomEtaleConstructible l E X n M →
      IsIso (finiteHomSiteHom l E X n K M) := by
  intro n K M hK hM
  classical
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  let : IsNoetherianRing (ULift.{u + 1, u} A) := isNoetherian_of_finite _ _
  let F := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X
  let : F.PreservesFlat := ProEtale.preservesFlat_comparisonUpperStar (X := X)
  let G := ProEtale.finiteCoefficientIntrinsicRealization X A
  have : G.IsEquivalence := (ProEtale.finiteCoefficientIntrinsicRealization_exact X A).1
  let R := G.mapDerivedCategory
  let d : finiteHomNu l E X n ≅ F.mapDerivedCategory ⋙ R :=
    (Functor.mapDerivedCategoryCompIso F G).symm
  let β := ProEtale.siteComparisonEvaluationHom
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X K M
  have hβ : IsIso β :=
    (finite_duality_site_comparison D l _hl E (n + 1) (Nat.succ_pos n) X).1 K M hK hM
  obtain ⟨e₀⟩ := ProEtale.intrinsicSiteHom_transport X A
    (F.mapDerivedCategory.obj K) (F.mapDerivedCategory.obj M)
  let e : (finiteHomNu l E X n).obj
      ((finiteHomEtaleInternalHom l E X n).obj (op K, M)) ≅
      (coefficientFiniteInternalHom l E X n).obj
        (op ((finiteHomNu l E X n).obj K), (finiteHomNu l E X n).obj M) :=
    d.app _ ≪≫ R.mapIso (@asIso _ _ _ _ β hβ) ≪≫ e₀ ≪≫
        (coefficientFiniteInternalHom l E X n).mapIso ((d.app K).op.prod (d.app M).symm)
  let : Fintype D.k₀ := Fintype.ofFinite _
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (by
    rw [← Nat.card_eq_fintype_card, D.card_base, D.cardinality_eq])
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  have hunit : IsUnit (algebraMap ℤ D.k (l : ℤ)) := by
    rw [map_natCast, isUnit_iff_ne_zero]
    exact CharP.cast_ne_zero_of_ne_of_prime _ (Fact.out : l.Prime) _hl.symm
  let : TopologicalSpace (ULift.{u + 1, u} A) := ⊥
  let : DiscreteTopology (ULift.{u + 1, u} A) := ⟨rfl⟩
  have hnil : ∃ r : ℕ, (l : ULift.{u + 1, u} A) ^ r = 0 := by
    have hs := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
    have hlmem : (l : Padic.coefficientExtensionIntegers l E) ∈
        Padic.coefficientExtensionMaximalIdeal l E := by
      apply (hs.2.1 _).mpr
      change spectralNorm ℚ_[l] E (l : E) < 1
      rw [← map_natCast (algebraMap ℚ_[l] E) l, spectralNorm_extends]
      exact Padic.norm_p_lt_one
    have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
        Set (Padic.coefficientExtensionIntegers l E)) =
        Padic.coefficientExtensionMaximalIdeal l E :=
      hs.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
    refine ⟨n + 1, ?_⟩
    apply ULift.down_injective
    change (l : A) ^ (n + 1) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change (l : Padic.coefficientExtensionIntegers l E) ^ (n + 1) ∈
      Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
        Set (Padic.coefficientExtensionIntegers l E)) ^ (n + 1)
    rw [hgen]
    exact Ideal.pow_mem_pow hlmem (n + 1)
  obtain ⟨ff⟩ := ProEtale.finiteComparisonOrdinary_fullyFaithful
    (ULift.{u + 1, u} A) D.k (Or.inr inferInstance) hunit hnil X
  let ffν := (ff.comp (Functor.FullyFaithful.ofFullyFaithful R)).ofIso d.symm
  exact siteHom_isIso_of_fullyFaithful
    (finiteHomEtaleClosed l E X n) (finiteIntrinsicClosed l E X n)
    (finiteHomNu l E X n) ffν (finiteHomNuTensor l E X n) K M e

end WeilConjectures
