/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import all WeilConjectures.SmoothPurity.Integral.IntegralTensorReductionTowerComparison
import all WeilConjectures.SmoothPurity.Integral.IntegralTensorTransitionCompatibility

/-! # Normalized strict integral tensor comparison

Source: Stacks 03EL and 07A4; Bhatt--Scholze, Definition 3.4.10.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.all false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures
open AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The tensor-reduction comparison has scalar normalization at every finite level.
Source: Stacks 03EL, 07A4; Bhatt--Scholze, Definition 3.4.10
(blueprint: lem-pur-normalized-integral-tensor-tower).
Proof: choose the existing finite tensor comparisons normalized on pure summands.
Their quotient-transition compatibility assembles them by NatTrans.ofOpSequence;
naturality in the pair of complexes assembles a natural isomorphism. Whisker by
the global slice/unrestricted tower comparison, whose finite components are identity
maps. Before scalar restriction, finite-coefficient linearity extends the unit-scalar
formula to every coefficient s, using s tensor z = s times (1 tensor z) and
bilinearity in the first tensor factor. The assembled components give the formula.
Uniqueness is proved separately by extensionality on scalar-extended total summands. -/
theorem normalizedIntegralTensorTower (W : Scheme.{t}) :
    ∃ d : (coefficientTotalTensor.{u, t + 1, t} (ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W) ⋙
        IntegralOnSlice.tower l E W none) ≅ integralOperationsTensorTowerFunctor l E W,
      ∀ (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) (p q : ℤ)
        (V : W.ProEtᵒᵖ) (s : (integralCoefficientCommRingSheaf l E W n).obj.obj V)
        (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
        (((d.hom.app (P, Q)).app (op n)).f (p + q)).val.app V
          (IntegralOnSlice.generator l E W none n _ V s
            (coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
              (completedIntegralCommRingSheafUnrestricted l E W) P Q p q (p + q) rfl V x y)) =
          integralOperationsTotalTensorSection l E W n P Q p q V
            (unrestrictedIntegralTensorSection l E W n (P.X p) V s x)
            (unrestrictedIntegralTensorSection l E W n (Q.X q) V 1 y) := by
  classical
  let T := coefficientTotalTensor.{u, t + 1, t} (ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)
  have h (n : ℕ) := finiteTensorComparison l E W n
  let b n := (h n).choose
  have hb (n : ℕ) (P Q : CochainComplex (integralTowerModules l E W) ℤ)
      (p q : ℤ) (V : W.ProEtᵒᵖ) (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V) :=
    (h n).choose_spec P Q p q V x y
  let c n := Functor.isoWhiskerRight (b n) (integralOperationsRestrict l E W n)
  let α (P : CochainComplex (integralTowerModules l E W) ℤ ×
      CochainComplex (integralTowerModules l E W) ℤ) :
      ((T ⋙ (Functor.ofOpSequence (unrestrictedIntegralTransition l E W)).flip).obj P) ⟶
        (integralOperationsTensorTowerFunctor l E W).obj P :=
    NatTrans.ofOpSequence (fun n ↦ (c n).hom.app P) (by
      intro n
      have hh := congrArg (fun φ ↦ NatTrans.app φ P)
        (integralTensorTransitionCompatibility l E W b hb n)
      simpa only [Functor.comp_obj, Functor.flip_obj_map,
        Functor.ofOpSequence_map_homOfLE_succ, NatTrans.comp_app,
        Functor.whiskerLeft_app, integralOperationsTensorTowerFunctor] using hh)
  have hα (P) : IsIso (α P) := by
    have hn (n : ℕᵒᵖ) : IsIso ((α P).app n) := by
      change IsIso ((c n.unop).hom.app P)
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  let d₀ : T ⋙ (Functor.ofOpSequence (unrestrictedIntegralTransition l E W)).flip ≅
      integralOperationsTensorTowerFunctor l E W :=
    NatIso.ofComponents (fun P ↦ @asIso _ _ _ _ (α P) (hα P)) (by
      intro P Q f
      apply NatTrans.ext
      funext n
      exact (c n.unop).hom.naturality f)
  let d := Functor.isoWhiskerLeft T
    (eqToIso (IntegralOnSlice.globalTower_eq l E W)) ≪≫ d₀
  refine ⟨d, ?_⟩
  intro P Q n p q V s x y
  change (((b n).hom.app (P, Q)).f (p + q)).val.app V
    (unrestrictedIntegralTensorSection l E W n _ V s
      (coefficientTensorGenerator.{u, t + 1, t} (ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W) P Q p q (p + q) rfl V x y)) = _
  let F := (unrestrictedIntegralReductionExistence l E W n).choose
  let hF := (unrestrictedIntegralReductionExistence l E W n).choose_spec.choose
  have hs := identifiedSection_smul
    (completedIntegralCommRingProjectionUnrestricted l E W n) F hF
    (((coefficientTotalTensor.{u, t + 1, t} (ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)).X (p + q)) V s
    (coefficientTensorGenerator.{u, t + 1, t} (ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W) P Q p q (p + q) rfl V x y)
  have hx := identifiedSection_smul
    (completedIntegralCommRingProjectionUnrestricted l E W n) F hF (P.X p) V s x
  have hg := tensorGenerator_smul_left.{t + 1, t, u}
    (R := integralCoefficientCommRingSheaf l E W n)
    ((unrestrictedIntegralFiniteComplex l E W n).obj P)
    ((unrestrictedIntegralFiniteComplex l E W n).obj Q) p q (p + q) rfl V s
    (unrestrictedIntegralTensorSection l E W n _ V 1 x)
    (unrestrictedIntegralTensorSection l E W n _ V 1 y)
  calc
    _ = (((b n).hom.app (P, Q)).f (p + q)).val.app V
        (s • unrestrictedIntegralTensorSection l E W n _ V 1
          (coefficientTensorGenerator.{u, t + 1, t} (ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l E W)
            P Q p q (p + q) rfl V x y)) :=
      congrArg ((((b n).hom.app (P, Q)).f (p + q)).val.app V) hs
    _ = s • (((b n).hom.app (P, Q)).f (p + q)).val.app V
        (unrestrictedIntegralTensorSection l E W n _ V 1
          (coefficientTensorGenerator.{u, t + 1, t} (ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted l E W)
            P Q p q (p + q) rfl V x y)) := map_smul _ s _
    _ = s • integralOperationsTotalTensorSection l E W n P Q p q V
        (unrestrictedIntegralTensorSection l E W n _ V 1 x)
        (unrestrictedIntegralTensorSection l E W n _ V 1 y) := by rw [hb]
    _ = integralOperationsTotalTensorSection l E W n P Q p q V
        (s • unrestrictedIntegralTensorSection l E W n _ V 1 x)
        (unrestrictedIntegralTensorSection l E W n _ V 1 y) := hg.symm
    _ = _ := congrArg
      (fun z ↦ integralOperationsTotalTensorSection l E W n P Q p q V z
        (unrestrictedIntegralTensorSection l E W n _ V 1 y)) hx.symm

end WeilConjectures
