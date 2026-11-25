/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.ConstantScalarTowerAdjunction
public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import all WeilConjectures.SmoothPurity.Completed.CompletedIntegralFiniteFree
import all WeilConjectures.CategoryTheory.SmoothPurity.AdicBasisLimit
import WeilConjectures.CategoryTheory.Constant.ConstantSpecifiedBasis
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Pushout square for completed constant coefficient maps

The finite-free completion comparison identifies the completed coefficient square
with the sectionwise pushout of the constant coefficient map and the two
constant-to-completion maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u r
open scoped BigOperators TensorProduct
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem sum_bijective_transport {A B A' B' : Type*}
    [Ring A] [Ring B] [Ring A'] [Ring B']
    (f : A →+* B) (f' : A' →+* B') (eA : A ≃+* A') (eB : B ≃+* B')
    (hf : ∀ a, eB (f a) = f' (eA a)) (n : ℕ) (v : Fin n → B)
    (hb : Function.Bijective (fun x : Fin n → A ↦ ∑ j, f (x j) * v j)) :
    Function.Bijective (fun x : Fin n → A' ↦ ∑ j, f' (x j) * eB (v j)) := by
  let e : (Fin n → A) ≃ (Fin n → A') := Equiv.piCongrRight (fun _ ↦ eA.toEquiv)
  have h (x : Fin n → A) :
      (∑ j, f' (e x j) * eB (v j)) = eB (∑ j, f (x j) * v j) := by
    simp only [map_sum, map_mul, hf]
    rfl
  constructor
  · intro x y hxy
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    exact congrArg e (hb.1 (eB.injective ((h x).symm.trans (hxy.trans (h y)))))
  · intro y
    obtain ⟨x, hx⟩ := hb.2 (eB.symm y)
    exact ⟨e x, (h x).trans ((congrArg eB hx).trans (eB.apply_symm_apply y))⟩

private theorem pushout_of_sum_bijective {A B C D : CommRingCat.{r}}
    (f : A ⟶ B) (g : A ⟶ C) (h : B ⟶ D) (k : C ⟶ D)
    (hw : f ≫ h = g ≫ k) (n : ℕ) (v : Fin n → B)
    (hb : Function.Bijective (fun x : Fin n → A ↦ ∑ j, f (x j) * v j))
    (hc : Function.Bijective (fun x : Fin n → C ↦ ∑ j, k (x j) * h (v j))) :
    IsPushout f g h k := by
  classical
  let := f.hom.toAlgebra
  let := g.hom.toAlgebra
  let := k.hom.toAlgebra
  let : Algebra A D := (k.hom.comp g.hom).toAlgebra
  let : IsScalarTower A C D := IsScalarTower.of_algebraMap_eq' rfl
  let L : (Fin n → A) →ₗ[A] B := Fintype.linearCombination A v
  have hL : Function.Bijective L := hb
  let b : Module.Basis (Fin n) A B :=
    Module.Basis.ofEquivFun (LinearEquiv.ofBijective L hL).symm
  have bv (j : Fin n) : b j = v j := by
    simp [b, L, Module.Basis.coe_ofEquivFun]
  let M : (Fin n → C) →ₗ[C] D := Fintype.linearCombination C (fun j ↦ h (v j))
  have hM : Function.Bijective M := hc
  let c : Module.Basis (Fin n) C D :=
    Module.Basis.ofEquivFun (LinearEquiv.ofBijective M hM).symm
  have cv (j : Fin n) : c j = h (v j) := by
    simp [c, M, Module.Basis.coe_ofEquivFun]
  let q : B →ₐ[A] D :=
    { __ := h.hom
      commutes' := fun a ↦ ConcreteCategory.congr_hom hw a }
  let m : C ⊗[A] B →ₐ[C] D := AlgHom.liftEquiv A C B D q
  let e := (b.baseChange C).equiv c (Equiv.refl _)
  have hm : m.toLinearMap = e.toLinearMap := by
    apply (b.baseChange C).ext
    intro j
    change m ((b.baseChange C) j) = (b.baseChange C).equiv c (Equiv.refl _) _
    rw [Module.Basis.equiv_apply, Module.Basis.baseChange_apply]
    simp only [m, AlgHom.liftEquiv_tmul, one_smul, bv, cv, Equiv.refl_apply]
    rfl
  have hm' : Function.Bijective m := by
    change Function.Bijective m.toLinearMap
    rw [hm]
    exact e.bijective
  let z := AlgEquiv.ofBijective m hm'
  exact (CommRingCat.isPushout_tensorProduct A C B).flip.of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) z.toCommRingCatIso
    (by ext; rfl) (by ext; rfl)
    (by ext x; simp [z, m, q])
    (by
      ext x
      change m (x ⊗ₜ 1) = k x
      rw [AlgHom.liftEquiv_tmul]
      change k x * h 1 = k x
      rw [map_one, mul_one])

section ModelSums
universe a b s
variable {Site : Type a} [Category.{b} Site] (J : GrothendieckTopology Site)
  (A B : Type (max a b s)) [CommRing A] [CommRing B] [Algebra A B]

private theorem constant_sum_bijective
    [HasSheafify J RingCat.{max a b s}]
    [HasSheafify J AddCommGrpCat.{max a b s}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max a b s}]
    (n : ℕ) (b : Module.Basis (Fin n) A B) (U : Siteᵒᵖ) :
    Function.Bijective (fun x : Fin n →
        ((constantSheaf J RingCat.{max a b s}).obj (RingCat.of A)).obj.obj U ↦
      ∑ j, ((constantSheaf J RingCat.{max a b s}).map
          (RingCat.ofHom (algebraMap A B))).hom.app U (x j) *
        (show ((constantSheaf J RingCat.{max a b s}).obj
          (RingCat.of B)).obj.obj U from
            (toSheafify J ((Functor.const Siteᵒᵖ).obj (RingCat.of B))).app U (b j))) := by
  obtain ⟨β, hβ⟩ := constantSheaf_specifiedBasis.{a, b, s} J A B n b
    (algebraMap A B) rfl
  let R := (constantSheaf J RingCat.{max a b s}).obj (RingCat.of A)
  let e := adicBasisFreeEquiv.{a, b, s} J R n U
  have hb := ((SheafOfModules.evaluation.{max a b s} R U).mapIso β).toLinearEquiv.bijective
  have hh := hb.comp e.symm.bijective
  have heq : (fun x ↦ β.hom.val.app U (e.symm x)) =
      (fun x : Fin n → R.obj.obj U ↦
        ∑ j, ((constantSheaf J RingCat.{max a b s}).map
          (RingCat.ofHom (algebraMap A B))).hom.app U (x j) *
            (show ((constantSheaf J RingCat.{max a b s}).obj
              (RingCat.of B)).obj.obj U from
                (toSheafify J ((Functor.const Siteᵒᵖ).obj (RingCat.of B))).app U (b j))) := by
    funext x
    rw [hβ]
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (fun z ↦ ((constantSheaf J RingCat.{max a b s}).map
      (RingCat.ofHom (algebraMap A B))).hom.app U z * _)
        ((adicBasisFreeEquiv_apply.{a, b, s} J R n U (e.symm x) j).symm.trans
          (congrFun (e.apply_symm_apply x) j))
  change Function.Bijective (fun x ↦ β.hom.val.app U (e.symm x)) at hh
  rw [heq] at hh
  exact hh

private theorem completed_sum_bijective (n : ℕ) (b : Module.Basis (Fin n) A B)
    (t : A) (v : B) (a : Bˣ) (e : ℕ) (he : 1 ≤ e)
    (ht : algebraMap A B t = (a : B) * v ^ e)
    (f : adicBasisCompletion.{a, b, s} J A t ⟶ adicBasisCompletion.{a, b, s} J B v)
    (hf : AdicBasisScalarCondition.{a, b, s} J t v a e he ht f) (U : Siteᵒᵖ) :
    Function.Bijective (fun x : Fin n → (adicBasisCompletion.{a, b, s} J A t).obj.obj U ↦
      ∑ j, f.hom.app U (x j) * (adicBasisCompletedUnit.{a, b, s} J v).app U (b j)) := by
  let E := adicBasisFreeEquiv.{a, b, s} J (adicBasisCompletion.{a, b, s} J A t) n U
  have hb : Function.Bijective
      ((adicBasisForward.{a, b, s} J n b t v f).val.app U) :=
    ⟨adicBasisForward_injective.{a, b, s} J n b t v a e he ht f hf U,
      adicBasisForward_surjective.{a, b, s} J n b t v a e he ht f hf U⟩
  have hh := hb.comp E.symm.bijective
  have heq : (fun x ↦ (adicBasisForward.{a, b, s} J n b t v f).val.app U (E.symm x)) =
      (fun x : Fin n → (adicBasisCompletion.{a, b, s} J A t).obj.obj U ↦
        ∑ j, f.hom.app U (x j) * (adicBasisCompletedUnit.{a, b, s} J v).app U (b j)) := by
    funext x
    rw [adicBasisForward_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [← adicBasisFreeEquiv_apply]
    exact congrArg (fun z ↦ f.hom.app U z * _) (congrFun (E.apply_symm_apply x) j)
  change Function.Bijective
    (fun x ↦ (adicBasisForward.{a, b, s} J n b t v f).val.app U (E.symm x)) at hh
  rw [heq] at hh
  exact hh
end ModelSums

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- `adicBasisRingSheafify` at the universes of the pro-étale site of `W`. -/
private local instance adicBasisRingSheafifyProEt (W : Scheme.{u}) :
    HasSheafify (ProEt.topology W) RingCat.{u + 1} :=
  adicBasisRingSheafify.{u + 1, u, u} _

private noncomputable def constantPresentation (W : Scheme.{u}) :
    (constantSheaf (ProEt.topology W) RingCat.{u + 1}).obj
      (RingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) ≅
      integralConstantRingOfUniverses l E W := by
  let : (ProEt.topology W).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
    scalarPreservesSheafification.{u, u} W
  exact ((constantCommuteCompose (ProEt.topology W)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))).symm

private theorem constantPresentation_completion (W : Scheme.{u}) :
    adicBasisFromConstant.{u + 1, u, u} (ProEt.topology W)
        (ULift.up (Padic.coefficientExtensionUniformizer l E)) ≫
        (completionPresentation l E W).hom =
      (constantPresentation l E W).hom ≫ integralConstantToCompletionOfUniverses l E W := by
  let : (ProEt.topology W).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
    scalarPreservesSheafification.{u, u} W
  apply limit.hom_ext
  intro n
  rw [Category.assoc, completionPresentation_projection, ← Category.assoc,
    adicBasisFromConstant_projection, Category.assoc]
  change _ = (constantPresentation l E W).hom ≫
    (integralConstantToCompletionOfUniverses l E W ≫
      limit.π (integralCoefficientSheafSystem l E W) n)
  rw [integralConstantToCompletionOfUniverses, limit.lift_π]
  let J := ProEt.topology W
  let CR := constantSheaf J RingCat.{u + 1}
  let CC := constantSheaf J CommRingCat.{u + 1}
  let FC := sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let c := constantCommuteCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  have h := mapped_square CR CC FC (forget₂ CommRingCat RingCat) c
    (Iso.refl (RingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))))
    (RingEquiv.toRingCatIso (liftedQuotient.{u, u}
      (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionUniformizer l E) (n.unop + 1)))
    (RingCat.ofHom (Ideal.Quotient.mk
      ((Ideal.span {ULift.up.{u + 1} (Padic.coefficientExtensionUniformizer l E)}) ^
        (n.unop + 1))))
    (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1}
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n.unop + 1)))))
    (by ext x; rfl)
  have hX : CR.map (Iso.refl
      (RingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))).hom = 𝟙 _ :=
    CR.map_id _
  rw [hX, Category.id_comp] at h
  exact h

/-- The completed coefficient square is a sectionwise pushout.

Source: Bhatt--Scholze, Lemma 6.8.2(1), together with the finite-free completed
scalar comparison.  At every pro-etale object, choose the integral E-basis of F
from the finite-free comparison.  Its compatible reductions identify the target
completed coefficient ring with the finite direct sum of copies of the source
completion indexed by that basis.  The resulting multiplication map is the
pushout of the constant map and the two constant-to-completion maps.  The
identification is compatible with restrictions because the coefficient maps are
constant and their residue normalizations determine the completion map uniquely;
therefore the sectionwise pushout condition follows from the universal property
of tensor product.  For an empty site object all four section rings are zero; for the identity
field extension the square is the identity square.  Both satisfy the same
universal property.
(blueprint: new-completed-constant-square-pushout).
-/
theorem completedConstantSquare_isPushout (W : Scheme.{u}) :
    ∀ U : W.ProEtᵒᵖ,
      IsPushout
        ((PurStrictScalar.constantMap l E F i W).hom.app U)
        (CommRingCat.ofHom (show
          ((PurStrictScalar.constants l E).ring W).obj.obj U →+*
            (completedIntegralCommRingSheafUnrestricted l E W).obj.obj U from
          ((integralConstantToCompletionOfUniverses l E W).hom.app U).hom))
        (CommRingCat.ofHom (show
          ((PurStrictScalar.constants l F).ring W).obj.obj U →+*
            (completedIntegralCommRingSheafUnrestricted l F W).obj.obj U from
          ((integralConstantToCompletionOfUniverses l F W).hom.app U).hom))
        ((completedCoefficientMap l E F i W).hom.app U) := by
  classical
  let := i.toAlgebra
  let := (integralScalarIntegerInclusion l E F i).toAlgebra
  let A := ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)
  let B := ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)
  let : Algebra A (Padic.coefficientExtensionIntegers l F) :=
    ULift.algebra' (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionIntegers l F)
  let t : A := ULift.up (Padic.coefficientExtensionUniformizer l E)
  let v : B := ULift.up (Padic.coefficientExtensionUniformizer l F)
  let J := ProEt.topology W
  let : HasSheafify J RingCat.{u + 1} := adicBasisRingSheafify.{u + 1, u, u} J
  let : J.PreservesSheafification (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
    scalarPreservesSheafification.{u, u} W
  let CR := constantSheaf J RingCat.{u + 1}
  let FC := sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  obtain ⟨b⟩ := integral_basis l E F i
  let n := Module.finrank E F
  let b' : Module.Basis (Fin n) A B := liftedBasis b
  obtain ⟨a, e, he, ht⟩ := integral_ramification l E F i
  let a' : Bˣ := Units.map ULift.ringEquiv.symm.toMonoidHom a
  have ht' : algebraMap A B t = (a' : B) * v ^ e := by
    apply ULift.ext
    exact ht
  obtain ⟨f, hf, _⟩ := adicBasisScalar_exists_unique.{u + 1, u, u} J t v a' e he ht'
  have hcomp : f ≫ (completionPresentation l F W).hom =
      (completionPresentation l E W).hom ≫ FC.map (completedCoefficientMap l E F i W) := by
    have hproj (L : Type u) [Field L] [Algebra ℚ_[l] L]
        [FiniteDimensional ℚ_[l] L] (m : ℕ) :
        FC.map (completedIntegralCommRingProjectionUnrestricted l L W m) =
          limit.π (integralCoefficientSheafSystem l L W) (op m) := by
      ext U x
      rfl
    apply limit.hom_ext
    intro m
    have hφ : completedCoefficientMap l E F i W ≫
        completedIntegralCommRingProjectionUnrestricted l F W m.unop =
      completedIntegralCommRingProjectionUnrestricted l E W m.unop ≫
        integralScalarQuotientSheafMap l E F i W m.unop :=
      (completedCoefficientMap_existsUnique l E F i W).exists.choose_spec m.unop
    have hφr := congrArg FC.map hφ
    simp only [Functor.map_comp, hproj] at hφr
    rw [Category.assoc, completionPresentation_projection, ← Category.assoc, hf m.unop,
      Category.assoc, finitePresentation_scalar l E W F i m.unop a' e he ht',
      ← Category.assoc, ← completionPresentation_projection, Category.assoc, ← hφr,
      ← Category.assoc]
  have hconst : CR.map (RingCat.ofHom (algebraMap A B)) ≫
        (constantPresentation l F W).hom =
      (constantPresentation l E W).hom ≫ FC.map (PurStrictScalar.constantMap l E F i W) := by
    exact (constantCommuteCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.naturality
        (CommRingCat.ofHom (integralScalarIntegerInclusion l E F i).ulift)
  have hmodel : CR.map (RingCat.ofHom (algebraMap A B)) ≫
        adicBasisFromConstant.{u + 1, u, u} J v =
      adicBasisFromConstant.{u + 1, u, u} J t ≫ f := by
    apply limit.hom_ext
    intro m
    change CR.map (RingCat.ofHom (algebraMap A B)) ≫
        adicBasisFromConstant.{u + 1, u, u} J v ≫
          adicBasisProjection.{u + 1, u, u} J B v m.unop =
      (adicBasisFromConstant.{u + 1, u, u} J t ≫ f) ≫
        adicBasisProjection.{u + 1, u, u} J B v m.unop
    rw [adicBasisFromConstant_projection, Category.assoc, hf m.unop,
      ← Category.assoc, adicBasisFromConstant_projection]
    unfold adicBasisScalar
    rw [← CR.map_comp, ← CR.map_comp]
    congr 1
  intro U
  let A₁ := ((PurStrictScalar.constants l E).ring W).obj.obj U
  let B₁ := ((PurStrictScalar.constants l F).ring W).obj.obj U
  let R₁ := (completedIntegralCommRingSheafUnrestricted l E W).obj.obj U
  let S₁ := (completedIntegralCommRingSheafUnrestricted l F W).obj.obj U
  let f₁ : A₁ ⟶ B₁ := (PurStrictScalar.constantMap l E F i W).hom.app U
  let g₁ : A₁ ⟶ R₁ :=
    @CommRingCat.ofHom A₁ R₁ (CommRingCat.commRing A₁) (CommRingCat.commRing R₁)
      (show A₁ →+* R₁ from
      ((integralConstantToCompletionOfUniverses l E W).hom.app U).hom)
  let h₁ : B₁ ⟶ S₁ :=
    @CommRingCat.ofHom B₁ S₁ (CommRingCat.commRing B₁) (CommRingCat.commRing S₁)
      (show B₁ →+* S₁ from
      ((integralConstantToCompletionOfUniverses l F W).hom.app U).hom)
  let k₁ : R₁ ⟶ S₁ := (completedCoefficientMap l E F i W).hom.app U
  let V := sheafToPresheaf J RingCat.{u + 1} ⋙
    (CategoryTheory.evaluation W.ProEtᵒᵖ RingCat.{u + 1}).obj U
  let eA : ((CR.obj (RingCat.of A)).obj.obj U) ≃+* A₁ :=
    (V.mapIso (constantPresentation l E W)).ringCatIsoToRingEquiv
  let eB : ((CR.obj (RingCat.of B)).obj.obj U) ≃+* B₁ :=
    (V.mapIso (constantPresentation l F W)).ringCatIsoToRingEquiv
  let eR : (adicBasisCompletion.{u + 1, u, u} J A t).obj.obj U ≃+* R₁ :=
    (V.mapIso (completionPresentation l E W)).ringCatIsoToRingEquiv
  let eS : (adicBasisCompletion.{u + 1, u, u} J B v).obj.obj U ≃+* S₁ :=
    (V.mapIso (completionPresentation l F W)).ringCatIsoToRingEquiv
  have hfU (x) : eB ((CR.map (RingCat.ofHom (algebraMap A B))).hom.app U x) =
      f₁ (eA x) := congrArg (fun q ↦ q.hom.app U x) hconst
  have hkU (x) : eS (f.hom.app U x) = k₁ (eR x) :=
    congrArg (fun q ↦ q.hom.app U x) hcomp
  have hgU (x) : eR ((adicBasisFromConstant.{u + 1, u, u} J t).hom.app U x) =
      g₁ (eA x) := by
    change (completionPresentation l E W).hom.hom.app U
        ((adicBasisFromConstant.{u + 1, u, u} J t).hom.app U x) =
      (integralConstantToCompletionOfUniverses l E W).hom.app U
        ((constantPresentation l E W).hom.hom.app U x)
    exact congrArg (fun q ↦ q.hom.app U x) (constantPresentation_completion l E W)
  have hhU (x) : eS ((adicBasisFromConstant.{u + 1, u, u} J v).hom.app U x) =
      h₁ (eB x) := by
    change (completionPresentation l F W).hom.hom.app U
        ((adicBasisFromConstant.{u + 1, u, u} J v).hom.app U x) =
      (integralConstantToCompletionOfUniverses l F W).hom.app U
        ((constantPresentation l F W).hom.hom.app U x)
    exact congrArg (fun q ↦ q.hom.app U x) (constantPresentation_completion l F W)
  have hw : f₁ ≫ h₁ = g₁ ≫ k₁ := by
    ext x
    obtain ⟨x, rfl⟩ := eA.surjective x
    change h₁ (f₁ (eA x)) = k₁ (g₁ (eA x))
    rw [← hfU, ← hhU, ← hgU, ← hkU]
    exact congrArg eS (congrArg (fun q ↦ q.hom.app U x) hmodel)
  let w : Fin n → (CR.obj (RingCat.of B)).obj.obj U := fun j ↦
    (toSheafify J ((Functor.const W.ProEtᵒᵖ).obj (RingCat.of B))).app U (b' j)
  have hb := sum_bijective_transport
    ((CR.map (RingCat.ofHom (algebraMap A B))).hom.app U).hom f₁.hom eA eB hfU n w
    (@constant_sum_bijective.{u + 1, u, u} W.ProEt inferInstance J A B
      inferInstance inferInstance inferInstance (adicBasisRingSheafify.{u + 1, u, u} J)
      (integralCoefficientAbSheafify.{u, u} W)
      (integralCoefficientAbLocallyBijective.{u, u} W) n b' U)
  have hc := sum_bijective_transport (f.hom.app U).hom k₁.hom eR eS hkU n
    (fun j ↦ (adicBasisCompletedUnit.{u + 1, u, u} J v).app U (b' j))
    (completed_sum_bijective.{u + 1, u, u} J A B n b' t v a' e he ht' f hf U)
  have hc' : Function.Bijective (fun x : Fin n → R₁ ↦
      ∑ j, k₁ (x j) * h₁ (eB (w j))) := by
    convert hc using 1
    funext x
    apply Finset.sum_congr rfl
    intro j _
    rw [← hhU]
    rfl
  exact pushout_of_sum_bijective f₁ g₁ h₁ k₁ hw n (fun j ↦ eB (w j)) hb hc'

end WeilConjectures
