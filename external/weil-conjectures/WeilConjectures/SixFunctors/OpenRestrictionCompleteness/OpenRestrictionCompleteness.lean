/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOpenReduction.IntegralOpenReductionDefinitions
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Sites.Proetale
import all WeilConjectures.Algebra.Homology.PrincipalConeExactEquivalence
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import all WeilConjectures.SixFunctors.Supporting.RoosIntrinsicCompletenessEquivalence
import WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
import WeilConjectures.SmoothPurity.IntegralPrincipalCone.IntegralPrincipalConeLocalCriterion
import Mathlib.Data.Nat.Prime.Infinite

/-! # Completeness of ordinary open restriction

Source: Stacks Project, Tags 08TC and 0941; immersion completed-pullback comparison.
The statement keeps independent universes for sites and coefficients.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.IntegralOpenReduction
namespace WeilConjectures.OpenRestrictionCompleteness

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]
  (o : Operations l E j)

private theorem principalMap
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    (F : A ⥤ B) [F.Additive] [HasCountableProducts A] [HasCountableProducts B]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    {P : CochainComplex A ℤ} (μ : End P) :
    ∃ c : (F.mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.PrincipalCone.completion μ) ≅
          CochainComplex.PrincipalCone.completion
            (End.of ((F.mapHomologicalComplex (.up ℤ)).map μ.asHom)),
      (F.mapHomologicalComplex (.up ℤ)).map (CochainComplex.PrincipalCone.unit μ) ≫
        c.hom = CochainComplex.PrincipalCone.unit
          (End.of ((F.mapHomologicalComplex (.up ℤ)).map μ.asHom)) := by
  classical
  let G := F.mapHomologicalComplex (.up ℤ)
  let ν := End.of (G.map μ.asHom)
  let K := fun n ↦ CochainComplex.PrincipalCone.level μ n
  let L := fun n ↦ CochainComplex.PrincipalCone.level ν n
  let e := CochainComplex.principalLevelIso F μ
  let p : G.obj (∏ᶜ K) ≅ ∏ᶜ L := PreservesProduct.iso G K ≪≫ Pi.mapIso e
  have hp (n : ℕ) : p.hom ≫ Pi.π L n = G.map (Pi.π K n) ≫ (e n).hom := by
    simp [p, PreservesProduct.iso_hom, Category.assoc]
  let f := CochainComplex.PrincipalCone.step μ
  let g := CochainComplex.PrincipalCone.step ν
  have hsq : G.map (towerTransitionEndomorphism f) ≫ p.hom =
      p.hom ≫ towerTransitionEndomorphism g := by
    apply Pi.hom_ext
    intro n
    rw [Category.assoc, hp, ← G.map_comp_assoc]
    simp only [towerTransitionEndomorphism, Preadditive.sub_comp,
      Category.id_comp, towerProductShift, Pi.lift_comp_π, G.map_sub,
      Preadditive.sub_comp, G.map_comp, Category.assoc,
      Preadditive.comp_sub, Category.comp_id, hp]
    rw [← Category.assoc p.hom, hp, Category.assoc]
    rw [← G.map_comp_assoc, Pi.lift_comp_π, G.map_comp, Category.assoc,
      CochainComplex.principalLevelIso_step F μ n]
  have hu : G.map (CochainComplex.PrincipalCone.productUnit μ) ≫ p.hom =
      CochainComplex.PrincipalCone.productUnit ν := by
    apply Pi.hom_ext
    intro n
    rw [Category.assoc, hp, ← G.map_comp_assoc]
    change G.map ((Pi.lift _) ≫ Pi.π K n) ≫ (e n).hom = _
    rw [Pi.lift_comp_π]
    change G.map _ ≫ (e n).hom = (Pi.lift _) ≫ Pi.π L n
    rw [Pi.lift_comp_π]
    exact CochainComplex.principalLevelIso_inr F μ n
  let c := CochainComplex.coneSquareIso (G.map (towerTransitionEndomorphism f))
    (towerTransitionEndomorphism g) p p hsq
  let i := CochainComplex.mapCoconeIso F (towerTransitionEndomorphism f) ≪≫
    (shiftFunctor _ (-1 : ℤ)).mapIso c
  refine ⟨i, ?_⟩
  change G.map _ ≫ (CochainComplex.mapCoconeIso F _).hom ≫ _ = _
  unfold CochainComplex.PrincipalCone.unit
  rw [← Category.assoc, CochainComplex.mapCoconeIso_lift F _ _
    (CochainComplex.PrincipalCone.productUnit_comp μ)]
  have hz : G.map (CochainComplex.PrincipalCone.productUnit μ) ≫
      G.map (towerTransitionEndomorphism f) = 0 := by
    rw [← G.map_comp]
    change G.map (CochainComplex.PrincipalCone.productUnit μ ≫
      CochainComplex.PrincipalCone.oneSubShift μ) = 0
    rw [CochainComplex.PrincipalCone.productUnit_comp, G.map_zero]
  exact (completedCoconeLift_natural B _ _ p.hom p.hom hsq (𝟙 _)
    (G.map (CochainComplex.PrincipalCone.productUnit μ))
    (CochainComplex.PrincipalCone.productUnit ν) hz
    (CochainComplex.PrincipalCone.productUnit_comp ν)
    (by simpa using hu.symm)).symm.trans (Category.id_comp _)

private theorem complete_iff_principal (T : Scheme.{t})
    (K : IntegralOnSlice.D l E T none) (Q : IntegralOnSlice.Cx l E T none)
    (e : DerivedCategory.Q.obj Q ≅ K) :
    complete l E T K ↔ IsIso (e.inv ≫ DerivedCategory.Q.map
      (CochainComplex.PrincipalCone.unit (WeilConjectures.integralKoszulScalar l E T Q))) := by
  classical
  let q := IntegralOnSlice.qGood l E T none
  let := IntegralOnSlice.goodLocalization l E T none
  let := Localization.essSurj q
    ((HomologicalComplex.quasiIso _ (.up ℤ)).inverseImage
      (IntegralOnSlice.Good l E T none).ι)
  let P := q.objPreimage K
  let eP : DerivedCategory.Q.obj P.obj ≅ K := q.objObjPreimageIso K
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hprime⟩
  obtain ⟨d, hd, _⟩ := WeilConjectures.PrincipalKoszulStrictReplacement.coefficient_datum l E
  have h := (WeilConjectures.roosIntrinsicCompletenessEquivalence p l (by omega)
    E T d hd K P eP).out 1 2
  change complete l E T K ↔ WeilConjectures.IntegralPrincipalCone.locallyComplete l E T
    (WeilConjectures.integralCompletionScalarValue l E T) K at h
  exact h.trans (WeilConjectures.IntegralPrincipalCone.localCriterion l E T
    (WeilConjectures.integralCompletionScalarValue l E T)
    (WeilConjectures.integralScalar_natural l E T) Q
    (WeilConjectures.integralKoszulScalar l E T Q)
    (WeilConjectures.integralKoszulScalar_existsUnique l E T Q).exists.choose_spec K e).2

private theorem scalar_projection (T : Scheme.{t}) (n : ℕ) (V : T.ProEtᵒᵖ) :
    (WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E T n).hom.app V
        (WeilConjectures.integralCompletionScalarValue l E T V) =
      (toSheafify (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of
          (ULift.{t+1} (Padic.coefficientExtensionRing l E (n+1)))))).app V
            (ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n+1))
              (Padic.coefficientExtensionUniformizer l E))) := by
  have h := congrArg (fun f ↦ f.hom.app V
    ((toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{t+1} (Padic.coefficientExtensionIntegers l E))))).app V
        (ULift.up (Padic.coefficientExtensionUniformizer l E))))
      (limit.lift_π (WeilConjectures.integralConstantConeOfUniverses l E T) (op n))
  change (WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E T n).hom.app V
    (WeilConjectures.integralCompletionScalarValue l E T V) =
      (WeilConjectures.integralConstantQuotientOfUniverses l E T n).hom.app V _ at h
  rw [h]
  let f : CommRingCat.of
      (ULift.{t+1} (Padic.coefficientExtensionIntegers l E)) ⟶
      CommRingCat.of (ULift.{t+1} (Padic.coefficientExtensionRing l E (n+1))) :=
    CommRingCat.ofHom (RingHom.ulift (Ideal.Quotient.mk
      (Padic.coefficientExtensionIdeal l E (n+1))))
  exact (congrArg (fun g ↦ g.app V
    (ULift.up (Padic.coefficientExtensionUniformizer l E)))
      (toSheafify_naturality (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).map f))).symm

private theorem scalar_transport (Z : Over (openObject j)) :
    o.completedMap.hom.app (op Z)
        (WeilConjectures.integralCompletionScalarValue l E X (op Z.left)) =
      WeilConjectures.integralCompletionScalarValue l E U (op ((sliceSite j).obj Z)) := by
  let D := WeilConjectures.integralCoefficientSheafSystem l E U
  let ev := sheafToPresheaf (ProEt.topology U) RingCat.{max u (t+1)} ⋙
    (evaluation U.ProEtᵒᵖ RingCat.{max u (t+1)}).obj (op ((sliceSite j).obj Z))
  apply Concrete.isLimit_ext (D ⋙ ev) (isLimitOfPreserves ev (limit.isLimit D))
  intro n
  obtain ⟨n⟩ := n
  have h := congrArg (fun f ↦ f.hom.app (op Z)
    (WeilConjectures.integralCompletionScalarValue l E X (op Z.left))) (o.projections n)
  change (WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E U n).hom.app
    (op ((sliceSite j).obj Z)) (o.completedMap.hom.app (op Z)
      (WeilConjectures.integralCompletionScalarValue l E X (op Z.left))) =
    (o.finiteMap n).hom.app (op Z)
    ((WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E X n).hom.app
      (op Z.left) (WeilConjectures.integralCompletionScalarValue l E X (op Z.left))) at h
  change (WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E U n).hom.app
    (op ((sliceSite j).obj Z)) _ = _
  change _ = (WeilConjectures.completedIntegralCommRingProjectionUnrestricted l E U n).hom.app
    (op ((sliceSite j).obj Z)) (WeilConjectures.integralCompletionScalarValue l E U
      (op ((sliceSite j).obj Z)))
  rw [h, scalar_projection, scalar_projection]
  exact congrArg (fun f ↦ f (ULift.up
    (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n+1))
      (Padic.coefficientExtensionUniformizer l E)))) (o.finiteConstants n Z)

private theorem inverse_scalar
    {C D : Type*} [Category* C] [Category* D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    {S : Sheaf J RingCat} {R : Sheaf K RingCat}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R)
    (e : SheafOfModules R ≌ SheafOfModules S)
    (he : e.functor = SheafOfModules.pushforward φ)
    (M : SheafOfModules S) (f : M ⟶ M)
    (g : e.inverse.obj M ⟶ e.inverse.obj M)
    (σ : ∀ V : Cᵒᵖ, S.obj.obj V) (τ : ∀ V : Dᵒᵖ, R.obj.obj V)
    (hf : ∀ V x, f.val.app V x = σ V • x)
    (hg : ∀ V x, g.val.app V x = τ V • x)
    (hσ : ∀ V, φ.hom.app V (σ V) = τ (F.op.obj V)) :
    e.inverse.map f = g := by
  apply e.functor.map_injective
  let c := e.counitIso.app M
  let i := (eqToIso he).app (e.inverse.obj M)
  let a := i.inv ≫ c.hom
  apply (cancel_mono c.hom).mp
  have hn := e.counitIso.hom.naturality f
  change e.functor.map (e.inverse.map f) ≫ c.hom = c.hom ≫ f at hn
  rw [hn]
  have hi := (eqToHom he).naturality g
  change e.functor.map g ≫ i.hom = i.hom ≫ (SheafOfModules.pushforward φ).map g at hi
  have h : (SheafOfModules.pushforward φ).map g ≫ a = a ≫ f := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    ext x
    change (a.val.app V) (g.val.app (F.op.obj V) x) =
      f.val.app V ((a.val.app V) x)
    rw [hg, hf, ← hσ V]
    exact (a.val.app V).hom.map_smul (σ V) x
  calc
    c.hom ≫ f = i.hom ≫ (a ≫ f) := by simp [a]
    _ = i.hom ≫ ((SheafOfModules.pushforward φ).map g ≫ a) := by rw [h]
    _ = e.functor.map g ≫ c.hom := by
      rw [← Category.assoc, ← hi]
      simp [a, Category.assoc]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem scalar_restriction (Q : IntegralOnSlice.Cx l E X none) :
    ((restriction l E j o).mapHomologicalComplex (.up ℤ)).map
        (WeilConjectures.integralKoszulScalar l E X Q).asHom =
      (WeilConjectures.integralKoszulScalar l E U
        (((restriction l E j o).mapHomologicalComplex (.up ℤ)).obj Q)).asHom := by
  apply HomologicalComplex.Hom.ext
  funext i
  let R := WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E U
  let S := (WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E X).over
    (openObject j)
  let φ : S ⟶ ((sliceSite j).sheafPushforwardContinuous RingCat
      ((ProEt.topology X).over (openObject j)) (ProEt.topology U)).obj R :=
    (sheafCompose ((ProEt.topology X).over (openObject j))
      (forget₂ CommRingCat.{max u (t+1)} RingCat.{max u (t+1)})).map o.completedMap
  let F := SheafOfModules.localizedSystemRestriction
    (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E X) (openObject j)
  refine inverse_scalar (S := S) (R := R) (sliceSite j) φ
    o.integral o.integralFunctor (F.obj (Q.X i))
    (F.map ((WeilConjectures.integralKoszulScalar l E X Q).asHom.f i))
    _ (fun V ↦ WeilConjectures.integralCompletionScalarValue l E X (op V.unop.left))
    (WeilConjectures.integralCompletionScalarValue l E U) ?_ ?_ ?_
  · intro V x
    exact (WeilConjectures.integralKoszulScalar_existsUnique l E X Q).exists.choose_spec
      i (op V.unop.left) x
  · intro V x
    exact (WeilConjectures.integralKoszulScalar_existsUnique l E U
      (((restriction l E j o).mapHomologicalComplex (.up ℤ)).obj Q)).exists.choose_spec i V x
  · intro V
    exact scalar_transport l E j o V.unop

/-- Ordinary open restriction preserves quotient-tower completeness, and its actual
completion unit is invertible on every such restriction.
Source: the open case of lem-sf-immersion-completed-pullback-comparison, Stacks
sites-cohomology.tex Tags 08TC, 0941, 07A4 and 0G7E.
(blueprint: lem-sf-open-restriction-completeness).

Proof: regard the open immersion as an immersion with identity closed factor.
Use the fixed coefficient maps and their quotient-projection equations to identify
ordinary open restriction with the immersion's exact ringed-site pullback. Restrict
one flat-term K-flat representative: exact restriction preserves its flat terms
and K-flatness. The quotient tensor identifications commute with every transition
and the scalar-unit augmentation. Restriction preserves the products in its Roos
triangle. Consequently the restricted augmented quotient triangle is the target
quotient triangle, which proves completeness. The completion comparison on this
good representative identifies its actual completion unit with the quotient
augmentation into the Roos complex. The distinguished quotient triangle makes
this map invertible. Transport along the representative isomorphisms by naturality
of the unit. All identifications use the fixed coefficient-equivalence units and
counits, so the result holds for the given operations. The empty open has the zero
module category; the identity open gives the original quotient triangle. -/
theorem openRestrictionComplete
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : U, Invertible (l : U.residueField x)] :
    ∀ H, complete l E X H →
      complete l E U ((star l E j o).obj H) ∧
      IsIso ((IntegralOnSlice.completionUnit l E U none).app
        ((star l E j o).obj H)) := by
  classical
  intro H hH
  let F := restriction l E j o
  let G := F.mapHomologicalComplex (.up ℤ)
  let Q := DerivedCategory.Q.objPreimage H
  let e : DerivedCategory.Q.obj Q ≅ H := DerivedCategory.Q.objObjPreimageIso H
  have hsrc := (complete_iff_principal l E X H Q e).mp hH
  have hi : IsIso (DerivedCategory.Q.map
      (CochainComplex.PrincipalCone.unit
        (WeilConjectures.integralKoszulScalar l E X Q))) := by
    let : IsIso (e.inv ≫ DerivedCategory.Q.map
      (CochainComplex.PrincipalCone.unit
        (WeilConjectures.integralKoszulScalar l E X Q))) := hsrc
    exact IsIso.of_isIso_comp_left e.inv _
  let : PreservesLimitsOfShape (Discrete ℕ) F :=
    (ordinaryAdjunction l E j o).rightAdjoint_preservesLimits.preservesLimitsOfShape
  have hμ : End.of (G.map (WeilConjectures.integralKoszulScalar l E X Q).asHom) =
      WeilConjectures.integralKoszulScalar l E U (G.obj Q) := by
    apply End.ext
    exact scalar_restriction l E j o Q
  have hm := principalMap F (WeilConjectures.integralKoszulScalar l E X Q)
  change ∃ c : G.obj _ ≅ CochainComplex.PrincipalCone.completion
      (End.of (G.map (WeilConjectures.integralKoszulScalar l E X Q).asHom)),
    G.map _ ≫ c.hom = CochainComplex.PrincipalCone.unit
      (End.of (G.map (WeilConjectures.integralKoszulScalar l E X Q).asHom)) at hm
  rw [hμ] at hm
  obtain ⟨c, hc⟩ := hm
  have hmap : IsIso (DerivedCategory.Q.map (G.map
      (CochainComplex.PrincipalCone.unit
        (WeilConjectures.integralKoszulScalar l E X Q)))) := by
    have hn := F.mapDerivedCategoryFactors.hom.naturality
      (CochainComplex.PrincipalCone.unit
        (WeilConjectures.integralKoszulScalar l E X Q))
    have ht : IsIso (F.mapDerivedCategory.map (DerivedCategory.Q.map
        (CochainComplex.PrincipalCone.unit
          (WeilConjectures.integralKoszulScalar l E X Q))) ≫
      F.mapDerivedCategoryFactors.hom.app _) := by infer_instance
    dsimp only [Functor.comp_map] at hn
    rw [hn] at ht
    let : IsIso (F.mapDerivedCategoryFactors.hom.app Q ≫
      DerivedCategory.Q.map (G.map (CochainComplex.PrincipalCone.unit
        (WeilConjectures.integralKoszulScalar l E X Q)))) := ht
    exact IsIso.of_isIso_comp_left (F.mapDerivedCategoryFactors.hom.app Q) _
  have htarget : IsIso (DerivedCategory.Q.map (CochainComplex.PrincipalCone.unit
      (WeilConjectures.integralKoszulScalar l E U (G.obj Q)))) := by
    rw [← hc, Functor.map_comp]
    infer_instance
  let er : DerivedCategory.Q.obj (G.obj Q) ≅ (star l E j o).obj H :=
    (F.mapDerivedCategoryFactors.app Q).symm ≪≫ F.mapDerivedCategory.mapIso e
  have hcomplete : complete l E U ((star l E j o).obj H) :=
    (complete_iff_principal l E U _ (G.obj Q) er).mpr (by infer_instance)
  refine ⟨hcomplete, ?_⟩
  let q := IntegralOnSlice.qGood l E U none
  let := IntegralOnSlice.goodLocalization l E U none
  let := Localization.essSurj q
    ((HomologicalComplex.quasiIso _ (.up ℤ)).inverseImage
      (IntegralOnSlice.Good l E U none).ι)
  let P := q.objPreimage ((star l E j o).obj H)
  let eP : q.obj P ≅ (star l E j o).obj H :=
    q.objObjPreimageIso _
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hprime⟩
  obtain ⟨d, hd, _⟩ := WeilConjectures.PrincipalKoszulStrictReplacement.coefficient_datum l E
  exact ((WeilConjectures.roosIntrinsicCompletenessEquivalence p l (by omega)
    E U d hd _ P eP).out 1 5).mp hcomplete

end WeilConjectures.OpenRestrictionCompleteness
