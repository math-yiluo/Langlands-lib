/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.PoincareDuality.Point.PointSectionsDerivedReductionData
public import WeilConjectures.Algebra.Homology.PrincipalReduction.Setup.DerivedReductionResolutionIndependence
import WeilConjectures.AlgebraicGeometry.Completed.CompletedIntegralScalarRegular
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedIntegralFiniteQuotientHomExt
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-! # The principal coefficient sequence at a pro-etale point
(blueprint: lem-pod-point-principal-reduction-coefficients) -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open SheafOfModules.PrincipalReduction

private theorem shortExact_of_app {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{u}]
    (S : ShortComplex (Sheaf J AddCommGrpCat.{u}))
    (h : ∀ U, ((S.map (sheafToPresheaf J AddCommGrpCat.{u})).map
      ((evaluation Cᵒᵖ AddCommGrpCat.{u}).obj U)).ShortExact) : S.ShortExact := by
  let F := sheafToPresheaf J AddCommGrpCat.{u}
  let K := S.map F
  have he : K.Exact := by
    apply (ShortComplex.exact_iff_isZero_homology _).2
    rw [IsZero.iff_id_eq_zero]
    apply NatTrans.ext
    funext U
    have hz := (ShortComplex.exact_iff_isZero_homology _).1 (h U).exact
    have hz' : IsZero (K.homology.obj U) :=
      hz.of_iso (K.mapHomologyIso ((evaluation Cᵒᵖ AddCommGrpCat.{u}).obj U)).symm
    exact hz'.eq_of_src _ _
  have hm : Mono K.f := (NatTrans.mono_iff_mono_app _).2 (fun U ↦ (h U).mono_f)
  have hg : Epi K.g := (NatTrans.epi_iff_epi_app _).2 (fun U ↦ (h U).epi_g)
  exact CategoryTheory.ShortExact.reflects_shortExact_of_faithful F ⟨he⟩

namespace WeilConjectures
local instance pointPrincipalSiteSmall (k : Type u) [Field k] :
    EssentiallySmall.{u + 1} (Spec (.of k)).ProEt := essentiallySmallSelf.{0} _
local instance pointPrincipalRingSheafify (k : Type u) [Field k] :
    HasSheafify (ProEt.topology (Spec (.of k))) CommRingCat.{u + 1} :=
  integralCoefficientRingSheafify.{u, u} (Spec (.of k))
local instance pointPrincipalAbSheafify (k : Type u) [Field k] :
    HasSheafify (ProEt.topology (Spec (.of k))) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} (Spec (.of k))
local instance pointPrincipalAbLocallyBijective (k : Type u) [Field k] :
    (ProEt.topology (Spec (.of k))).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} (Spec (.of k))

/-- The completed integral coefficient projection is the cokernel of the indicated
uniformizer power, which is injective on every object's sections.

Proof: restriction of a constant scalar remains that same scalar. The finite projection
kills its (n+1)st power. Its kernel consists exactly of multiples of that power by
completedIntegralProjection_divisible. Injectivity follows by testing finite projections
at levels r+n+1, where multiplication identifies the rth quotient with a submodule.
The constant quotient map is sectionwise surjective and factors through completion,
so the completed projection is sectionwise surjective as well. Objectwise exactness
then implies exactness of presheaves and hence of sheaves.
Source: Stacks Tags 093J--093M and 06YY; original blueprint step 1.
(blueprint: lem-pod-point-principal-reduction-coefficients) -/
theorem pointPrincipalReductionCoefficients (k : Type u) [Field k]
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    let U := ProEt.mk (𝟙 (Spec (.of k)))
    let O := completedIntegralCommRingSheafUnrestricted l E (Spec (.of k))
    let μ := sectionMultiplication O U
      (MorphismProperty.Over.mkIdTerminal @WeaklyEtale (Spec (.of k)))
      (pointIntegralSectionMap l E k
        (ULift.up (Padic.coefficientExtensionUniformizer l E) ^ (n + 1)))
    let φ := (sheafCompose (ProEt.topology (Spec (.of k)))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map
      (completedIntegralCommRingProjectionUnrestricted l E (Spec (.of k)) n)
    ∃ hz : μ ≫ φ = 0, (ShortComplex.mk μ φ hz).ShortExact := by
  let T := Spec (.of k)
  let J := ProEt.topology T
  let U := ProEt.mk (𝟙 T)
  let hU := MorphismProperty.Over.mkIdTerminal @WeaklyEtale T
  let O := completedIntegralCommRingSheafUnrestricted l E T
  let π := Padic.coefficientExtensionUniformizer l E
  let c := integralConstantToCompletionOfUniverses l E T
  let a (V : T.ProEtᵒᵖ) := (toSheafify J ((Functor.const T.ProEtᵒᵖ).obj
    (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))))).app V
      (ULift.up π)
  let s (V : T.ProEtᵒᵖ) : O.obj.obj V := c.hom.app V (a V)
  let p := completedIntegralCommRingProjectionUnrestricted l E T n
  let μ := sectionMultiplication O U hU
    (pointIntegralSectionMap l E k (ULift.up π ^ (n + 1)))
  let φ := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
    forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map p
  have hμ (V : T.ProEtᵒᵖ) (x : O.obj.obj V) :
      μ.hom.app V x = s V ^ (n + 1) * x := by
    have hm := (existsUnique_sectionMultiplication O U hU
      (pointIntegralSectionMap l E k (ULift.up π ^ (n + 1)))).exists.choose_spec V.unop x
    erw [hm]
    congr 1
    change O.obj.map (hU.from V.unop).op
      (c.hom.app (op U) ((toSheafify J ((Functor.const T.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))))).app
          (op U) (ULift.up π ^ (n + 1)))) = _
    let η := toSheafify J ((Functor.const T.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))))
    let t := (ULift.up π ^ (n + 1) : ULift.{u + 1} _)
    have hc := congrArg (fun h ↦ h (η.app (op U) t))
      (c.hom.naturality (hU.from V.unop).op)
    have hη := congrArg (fun h ↦ h t) (η.naturality (hU.from V.unop).op)
    change η.app V t =
      (integralConstantRingOfUniverses l E T).obj.map (hU.from V.unop).op
        (η.app (op U) t) at hη
    change c.hom.app V ((integralConstantRingOfUniverses l E T).obj.map
        (hU.from V.unop).op (η.app (op U) t)) =
      O.obj.map (hU.from V.unop).op (c.hom.app (op U) (η.app (op U) t)) at hc
    calc
      _ = c.hom.app V ((integralConstantRingOfUniverses l E T).obj.map
          (hU.from V.unop).op (η.app (op U) t)) := hc.symm
      _ = c.hom.app V (η.app V t) := congrArg (c.hom.app V) hη.symm
      _ = s V ^ (n + 1) := by rw [map_pow, map_pow]
  have hps (V : T.ProEtᵒᵖ) : p.hom.app V (s V ^ (n + 1)) = 0 := by
    have hc := congrArg (fun h ↦ h.hom.app V (a V ^ (n + 1)))
      (limit.lift_π (integralConstantConeOfUniverses l E T) (op n))
    change p.hom.app V (c.hom.app V (a V ^ (n + 1))) = _ at hc
    rw [map_pow] at hc
    rw [hc]
    let R := CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
    let B := CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
    let q : R ⟶ B := CommRingCat.ofHom (RingHom.ulift (Ideal.Quotient.mk
      (Padic.coefficientExtensionIdeal l E (n + 1))))
    let η := toSheafify J ((Functor.const T.ProEtᵒᵖ).obj R)
    let η' := toSheafify J ((Functor.const T.ProEtᵒᵖ).obj B)
    have hn := congrArg (fun h ↦ h.app V (ULift.up π ^ (n + 1)))
      (toSheafify_naturality J ((Functor.const T.ProEtᵒᵖ).map q))
    change η'.app V (q (ULift.up π ^ (n + 1))) =
      (integralConstantQuotientOfUniverses l E T n).hom.app V
        (η.app V (ULift.up π ^ (n + 1))) at hn
    have ht : q (ULift.up π ^ (n + 1)) = 0 := by
      apply ULift.ext
      change Ideal.Quotient.mk _ (π ^ (n + 1)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, Padic.coefficientExtensionIdeal]
      exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton π)) _
    have ha : a V ^ (n + 1) = η.app V (ULift.up π ^ (n + 1)) :=
      (map_pow (η.app V).hom (ULift.up π) (n + 1)).symm
    erw [ha, ← hn, ht, map_zero]
  have hz : μ ≫ φ = 0 := by
    ext V x
    change p.hom.app V (μ.hom.app V x) = 0
    rw [hμ, map_mul, hps, zero_mul]
  refine ⟨hz, ?_⟩
  apply shortExact_of_app J
  intro V
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.ab_exact_iff _).2
    intro x hx
    change p.hom.app V x = 0 at hx
    obtain ⟨y, hy⟩ := completedIntegralProjection_divisible l E T n V x hx
    exact ⟨y, (hμ V y).trans hy.symm⟩
  · apply (AddCommGrpCat.mono_iff_injective _).2
    intro x y hxy
    apply completedIntegralScalar_regular l E T (n + 1) V
    exact (hμ V x).symm.trans (hxy.trans (hμ V y))
  · apply (AddCommGrpCat.epi_iff_surjective _).2
    intro x
    obtain ⟨y, hy⟩ := constantQuotient_surjective l E T n V x
    refine ⟨c.hom.app V y, ?_⟩
    exact (congrArg (fun h ↦ h.hom.app V y)
      (limit.lift_π (integralConstantConeOfUniverses l E T) (op n))).trans hy

end WeilConjectures
