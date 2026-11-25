/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedLineTensorOrdinaryData
import WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionDualEvaluation
import all WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedLineTensorOrdinaryData
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison

/-! # Scalar extension of signed powers of a coefficient line

Source: Stacks 03EK, 03EO, 0GMX; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).

A comparison `b` between the scalar extension of a line `L` and a line `N` induces
comparisons of all signed powers: positive powers by the binary tensor comparison and
`b`, negative powers by duality. They are uniquely fixed by the positive formula and the
pairing formula, and they are compatible with a tower of three coefficient fields.

## Main definitions and statements

* `IsLineNormalized`: the positive-power formula and the pairing formula.
* `line_exists`, `line_unique`: normalized signed-power comparisons exist and are unique.
* `line_tower`: the comparisons for a three-field tower compose.
-/

@[expose] public noncomputable section
set_option Elab.async false
attribute [local instance 5000] CategoryTheory.HasSheafify.isRightAdjoint
attribute [local instance 5000] Algebra.toModule
attribute [local irreducible] Padic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] HasDerivedCategory.standard
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
universe t u uC vC w
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
namespace WeilConjectures
namespace CompletedLineTensor

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted completedCoefficientMap
  completedOrdinaryScalarExtension completedDerivedScalarExtension
  completedScalarCounit completedScalarTensorSection integralScalarExtensionOfUniverses
  completedScalarChangeData completedOrdinaryScalarComplex

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})
variable (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] F)

/-- Comparisons of all signed powers after scalar extension.
Source: Stacks 03EK (blueprint: lem-pur-completed-line-tensor-coherence). -/
abbrev LineFamily (L : integralTowerModules l E X) (N : integralTowerModules l F X) :=
  ∀ m : ℤ, SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
    (completedCoefficientMap l E F ι X) (power l E X L m) ≅ power l F X N m

/-- The positive-power formula and the pairing formula of `IsPairNormalized`.
Source: Stacks 03EL, 03EO; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence). -/
def IsLineNormalized (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (N : integralTowerModules l F X) [N.IsFiniteLocallyFreeOfRank 1]
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N)
    (B : LineFamily l E X F ι L N) : Prop :=
  (∀ n : ℕ,
    (B (Int.ofNat n)).hom = ((binary l E X F ι).power L n).hom ≫
      SheafOfModules.scalarTensorPowerMap.{t + 1, t, max u (t + 1)}
        (completedIntegralCommRingSheafUnrestricted l F X) b.hom n) ∧
  (∀ (n : ℕ) (U : X.ProEtᵒᵖ)
      (s t : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
      (f : (power l E X L (-Int.ofNat (n + 1))).val.obj U)
      (x : (power l E X L (Int.ofNat (n + 1))).val.obj U),
    pairing l F X N (Int.ofNat (n + 1)) U
      ((B (Int.ofNat (n + 1))).hom.val.app U
        (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
          (completedCoefficientMap l E F ι X) _ U t x))
      ((B (-Int.ofNat (n + 1))).hom.val.app U
        (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
          (completedCoefficientMap l E F ι X) _ U s f)) =
      s * t * (completedCoefficientMap l E F ι X).hom.app U
        (pairing l E X L (Int.ofNat (n + 1)) U x f))

section Generic

open SheafOfModules

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max uC vC w} RingCat.{max uC vC w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC w}]
  [HasWeakSheafify J AddCommGrpCat.{max uC vC w}]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] siteSheafTensorRight siteSheafTensorTmul
  siteSheafTensorSecondMap scalarExtensionDualMap changeOfRingsOfUniverses
  changeOfRingsHomOfUniverses scalarExtensionLift scalarExtensionSection
  scalarTensorBinaryIso scalarTensorBinaryForward scalarTensorBinaryInverse
  scalarTensorLeftUnitor scalarExtensionUnitIso
  scalarExtensionTowerForward scalarExtensionTowerReverse

/-- Positive-power comparisons normalized by the unit comparison in degree zero, the given
line comparison in degree one, and the pure-tensor recursion.
Source: Stacks 03EK (blueprint: lem-pur-completed-line-tensor-coherence). -/
private def IsPositiveNormalized {R S : Sheaf J CommRingCat.{max uC vC w}} (α : R ⟶ S)
    (L : SheafOfModules.{max uC vC w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (K : SheafOfModules.{max uC vC w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (b : changeOfRingsOfUniverses α L ≅ K)
    (P : ∀ n : ℕ, changeOfRingsOfUniverses α (scalarTensorPower R L n) ⟶
      scalarTensorPower S K n) : Prop :=
  P 0 = (scalarExtensionUnitIso α).hom ∧ P 1 = b.hom ∧
  ∀ (n : ℕ) (U : Cᵒᵖ) (s : S.obj.obj U) (x : (scalarTensorPower R L (n + 1)).val.obj U)
    (y : L.val.obj U),
    (P (n + 2)).val.app U (scalarExtensionSection α (scalarTensorPower R L (n + 2)) U s
        (siteSheafTensorTmul (scalarTensorPower R L (n + 1)) L U x y)) =
      siteSheafTensorTmul (scalarTensorPower S K (n + 1)) K U
        ((P (n + 1)).val.app U
          (scalarExtensionSection α (scalarTensorPower R L (n + 1)) U s x))
        (b.hom.val.app U (scalarExtensionSection α L U 1 y))

/-- The binary tensor comparison followed by tensor powers of `b` is normalized.
Source: Stacks 03EK (blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem isPositiveNormalized_binary {R S : Sheaf J CommRingCat.{max uC vC w}}
    (α : R ⟶ S)
    (L : SheafOfModules.{max uC vC w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (K : SheafOfModules.{max uC vC w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (b : changeOfRingsOfUniverses α L ≅ K) (e : ScalarExtensionTensorCore R S α) :
    IsPositiveNormalized α L K b
      (fun n ↦ (e.power L n).hom ≫ scalarTensorPowerMap S b.hom n) := by
  refine ⟨Category.comp_id _, Category.id_comp _, ?_⟩
  intro n U s x y
  have h1 : (e.power L (n + 2)).hom = (e.tensorComparison _ L).hom ≫
      (siteSheafTensorRight _).map (e.power L (n + 1)).hom := rfl
  have h2 : scalarTensorPowerMap S b.hom (n + 2) =
      (siteSheafTensorRight _).map (scalarTensorPowerMap S b.hom (n + 1)) ≫
        siteSheafTensorSecondMap _ b.hom := rfl
  dsimp only
  rw [h1, h2]
  simp only [Category.assoc, comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [e.tensor_tmul, scalarTensor_first_tmul, scalarTensor_first_tmul,
    scalarTensor_second_tmul]

/-- Normalized positive-power comparisons are unique.
Source: Stacks 03EK (blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem isPositiveNormalized_unique {R S : Sheaf J CommRingCat.{max uC vC w}}
    (α : R ⟶ S)
    (L : SheafOfModules.{max uC vC w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (K : SheafOfModules.{max uC vC w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (b : changeOfRingsOfUniverses α L ≅ K)
    {P Q : ∀ n : ℕ, changeOfRingsOfUniverses α (scalarTensorPower R L n) ⟶
      scalarTensorPower S K n}
    (hP : IsPositiveNormalized α L K b P) (hQ : IsPositiveNormalized α L K b Q) : P = Q := by
  funext n
  induction n using Nat.twoStepInduction with
  | zero => exact hP.1.trans hQ.1.symm
  | one => exact hP.2.1.trans hQ.2.1.symm
  | more n _ ih =>
    apply scalarExtension_tensor_hom_ext α (scalarTensorPower R L (n + 1)) L
    intro U s x y
    refine (hP.2.2 n U s x y).trans (Eq.trans ?_ (hQ.2.2 n U s x y).symm)
    rw [ih]

/-- Normalized positive-power comparisons compose along a tower of coefficient rings.
Source: Stacks 03EK (blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem isPositiveNormalized_tower {R S T : Sheaf J CommRingCat.{max uC vC w}}
    (α : R ⟶ S) (β : S ⟶ T) (γ : R ⟶ T) (hγ : α ≫ β = γ)
    (L : SheafOfModules.{max uC vC w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (K : SheafOfModules.{max uC vC w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (P : SheafOfModules.{max uC vC w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj T))
    (b10 : changeOfRingsOfUniverses α L ≅ K) (b21 : changeOfRingsOfUniverses β K ≅ P)
    (b20 : changeOfRingsOfUniverses γ L ≅ P)
    (hb : ∀ (U : Cᵒᵖ) (s : S.obj.obj U) (t : T.obj.obj U) (x : L.val.obj U),
      b21.hom.val.app U (scalarExtensionSection β K U t
        (b10.hom.val.app U (scalarExtensionSection α L U s x))) =
      b20.hom.val.app U (scalarExtensionSection γ L U (t * β.hom.app U s) x))
    {P10 : ∀ n : ℕ, changeOfRingsOfUniverses α (scalarTensorPower R L n) ⟶
      scalarTensorPower S K n}
    {P21 : ∀ n : ℕ, changeOfRingsOfUniverses β (scalarTensorPower S K n) ⟶
      scalarTensorPower T P n}
    {P20 : ∀ n : ℕ, changeOfRingsOfUniverses γ (scalarTensorPower R L n) ⟶
      scalarTensorPower T P n}
    (h10 : IsPositiveNormalized α L K b10 P10) (h21 : IsPositiveNormalized β K P b21 P21)
    (h20 : IsPositiveNormalized γ L P b20 P20)
    (n : ℕ) (U : Cᵒᵖ) (s : S.obj.obj U) (t : T.obj.obj U)
    (a : (scalarTensorPower R L n).val.obj U) :
    (P21 n).val.app U (scalarExtensionSection β _ U t
      ((P10 n).val.app U (scalarExtensionSection α _ U s a))) =
      (P20 n).val.app U (scalarExtensionSection γ _ U (t * β.hom.app U s) a) := by
  subst hγ
  have pt (k : ℕ) (hk : changeOfRingsHomOfUniverses β _ (P10 k) ≫ P21 k =
      scalarExtensionTowerForward α β (scalarTensorPower R L k) ≫ P20 k)
      (U : Cᵒᵖ) (s : S.obj.obj U) (t : T.obj.obj U)
      (a : (scalarTensorPower R L k).val.obj U) :
      (P21 k).val.app U (scalarExtensionSection β _ U t
        ((P10 k).val.app U (scalarExtensionSection α _ U s a))) =
        (P20 k).val.app U (scalarExtensionSection (α ≫ β) _ U (t * β.hom.app U s) a) := by
    have h := congrArg (fun f ↦ f.val.app U (scalarExtensionSection β _ U t
      (scalarExtensionSection α _ U s a))) hk
    simp only [comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply] at h
    rwa [scalarExtension_map_tmul, scalarExtensionTowerForward_tmul] at h
  suffices key : ∀ k : ℕ, changeOfRingsHomOfUniverses β _ (P10 k) ≫ P21 k =
      scalarExtensionTowerForward α β (scalarTensorPower R L k) ≫ P20 k from
    pt n (key n) U s t a
  clear U s t a
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
    apply scalarExtensionTower_hom_ext α β
    intro U t s a
    simp only [comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
    rw [scalarExtension_map_tmul, scalarExtensionTowerForward_tmul, h10.1, h21.1, h20.1]
    erw [scalarExtensionUnitIso_tmul, scalarExtensionUnitIso_tmul,
      scalarExtensionUnitIso_tmul]
    rw [map_mul, mul_assoc]
    rfl
  | one =>
    apply scalarExtensionTower_hom_ext α β
    intro U t s a
    simp only [comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
    rw [scalarExtension_map_tmul, scalarExtensionTowerForward_tmul, h10.2.1, h21.2.1,
      h20.2.1]
    exact hb U s t a
  | more n _ ih =>
    have hr : scalarExtensionTowerReverse α β _ ≫
        (changeOfRingsHomOfUniverses β _ (P10 (n + 2)) ≫ P21 (n + 2)) =
        scalarExtensionTowerReverse α β _ ≫
          (scalarExtensionTowerForward α β _ ≫ P20 (n + 2)) := by
      rw [← Category.assoc (scalarExtensionTowerReverse α β _)
        (scalarExtensionTowerForward α β _),
        scalarExtensionTower_reverse_forward, Category.id_comp]
      apply scalarExtension_tensor_hom_ext (α ≫ β) (scalarTensorPower R L (n + 1)) L
      intro U c x y
      simp only [comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
      erw [scalarExtensionTowerReverse_tmul, scalarExtension_map_tmul]
      erw [h10.2.2 n U 1 x y, h21.2.2 n U c, h20.2.2 n U c x y]
      have h1 := pt (n + 1) ih U 1 c x
      have h2 := hb U 1 1 y
      rw [map_one, mul_one] at h1 h2
      rw [h1, h2]
    have h := congrArg (fun f ↦ scalarExtensionTowerForward α β _ ≫ f) hr
    simpa only [← Category.assoc, scalarExtensionTower_forward_reverse,
      Category.id_comp] using h

/-- Restriction of the value of a map out of a scalar extension on a pure section.
Source: Stacks 03EK (blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem scalarExtension_hom_restrict {R S : Sheaf J CommRingCat.{max uC vC w}}
    (α : R ⟶ S)
    (M : SheafOfModules.{max uC vC w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    {H : SheafOfModules.{max uC vC w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)}
    (D : changeOfRingsOfUniverses α M ⟶ H) {U V : Cᵒᵖ} (i : U ⟶ V)
    (s : S.obj.obj U) (f : M.val.obj U) :
    H.val.map i (D.val.app U (scalarExtensionSection α M U s f)) =
      D.val.app V (scalarExtensionSection α M V (S.obj.map i s) (M.val.map i f)) := by
  rw [← PresheafOfModules.naturality_apply, scalarExtensionSection_naturality]

/-- A section of the dual of `N` is determined by its values, after all restrictions, on
the images of pure sections under a comparison `changeOfRings α M ≅ N`.
Source: Stacks 03EK, 04TT (blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem homObj_section_ext {R S : Sheaf J CommRingCat.{max uC vC w}}
    (α : R ⟶ S)
    (M : SheafOfModules.{max uC vC w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (N : SheafOfModules.{max uC vC w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (e : changeOfRingsOfUniverses α M ≅ N) (U : Cᵒᵖ)
    (φ ψ : (homObj N (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))).val.obj U)
    (h : ∀ (V : Cᵒᵖ) (i : U ⟶ V) (t : S.obj.obj V) (x : M.val.obj V),
      ((homObj N (unit _)).val.map i φ).app (op (Over.mk (𝟙 V.unop)))
          (e.hom.val.app V (scalarExtensionSection α M V t x)) =
        ((homObj N (unit _)).val.map i ψ).app (op (Over.mk (𝟙 V.unop)))
          (e.hom.val.app V (scalarExtensionSection α M V t x))) : φ = ψ := by
  have hc : homObjMap e.hom
      (𝟙 (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))) ≫
      homObjMap e.inv (𝟙 (unit _)) = 𝟙 _ := by
    rw [homObjMap_comp_homObjMap, e.inv_hom_id, Category.comp_id, homObjMap_id]
  have hφ := congrArg (fun f ↦ f.val.app U φ) hc
  have hψ := congrArg (fun f ↦ f.val.app U ψ) hc
  simp only [comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply, id_val,
    PresheafOfModules.id_app, ModuleCat.id_apply] at hφ hψ
  rw [← hφ, ← hψ]
  congr 1
  apply scalarDual_section_ext α M U
  intro W t x
  have hW := h (op W.unop.left) W.unop.hom.op t x
  exact (PresheafOfModules.restrictOver_hom_app_congr φ (Category.id_comp W.unop.hom).symm
    _).trans (hW.trans (PresheafOfModules.restrictOver_hom_app_congr ψ
      (Category.id_comp W.unop.hom) _))

/-- A dual comparison is determined by its evaluation against a positive comparison.
Source: Stacks 03EK, 04TT (blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem dualComparison_ext {R S : Sheaf J CommRingCat.{max uC vC w}}
    (α : R ⟶ S)
    (M : SheafOfModules.{max uC vC w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (N : SheafOfModules.{max uC vC w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (e : changeOfRingsOfUniverses α M ≅ N)
    (D D' : changeOfRingsOfUniverses α
        (homObj M (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) ⟶
      homObj N (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)))
    (hD : ∀ (U : Cᵒᵖ) (s t : S.obj.obj U)
      (f : (homObj M (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))).val.obj U)
      (x : M.val.obj U),
      (D.val.app U (scalarExtensionSection α _ U s f)).app (op (Over.mk (𝟙 U.unop)))
          (e.hom.val.app U (scalarExtensionSection α M U t x)) =
        (D'.val.app U (scalarExtensionSection α _ U s f)).app (op (Over.mk (𝟙 U.unop)))
          (e.hom.val.app U (scalarExtensionSection α M U t x))) : D = D' := by
  apply scalarExtension_hom_ext α _
  intro U s f
  apply homObj_section_ext α M N e U
  intro V i t x
  rw [scalarExtension_hom_restrict, scalarExtension_hom_restrict]
  exact hD V _ t _ x

/-- Dual comparisons normalized by evaluation compose along a tower of coefficient rings.
Source: Stacks 03EK, 04TT (blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem dualComparison_tower {R S T : Sheaf J CommRingCat.{max uC vC w}}
    (α : R ⟶ S) (β : S ⟶ T) (γ : R ⟶ T) (hγ : α ≫ β = γ)
    (M : SheafOfModules.{max uC vC w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (N : SheafOfModules.{max uC vC w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (P : SheafOfModules.{max uC vC w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj T))
    (e10 : changeOfRingsOfUniverses α M ≅ N) (e21 : changeOfRingsOfUniverses β N ≅ P)
    (e20 : changeOfRingsOfUniverses γ M ≅ P)
    (he : ∀ (U : Cᵒᵖ) (t : T.obj.obj U) (x : M.val.obj U),
      e21.hom.val.app U (scalarExtensionSection β N U t
        (e10.hom.val.app U (scalarExtensionSection α M U 1 x))) =
      e20.hom.val.app U (scalarExtensionSection γ M U t x))
    (D10 : changeOfRingsOfUniverses α
        (homObj M (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) ⟶
      homObj N (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)))
    (D21 : changeOfRingsOfUniverses β
        (homObj N (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))) ⟶
      homObj P (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj T)))
    (D20 : changeOfRingsOfUniverses γ
        (homObj M (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) ⟶
      homObj P (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj T)))
    (h10 : ∀ (U : Cᵒᵖ) (s t : S.obj.obj U)
      (f : (homObj M (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))).val.obj U)
      (x : M.val.obj U),
      (D10.val.app U (scalarExtensionSection α _ U s f)).app (op (Over.mk (𝟙 U.unop)))
          (e10.hom.val.app U (scalarExtensionSection α M U t x)) =
        s * t * α.hom.app U (f.app (op (Over.mk (𝟙 U.unop))) x))
    (h21 : ∀ (U : Cᵒᵖ) (s t : T.obj.obj U)
      (f : (homObj N (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))).val.obj U)
      (x : N.val.obj U),
      (D21.val.app U (scalarExtensionSection β _ U s f)).app (op (Over.mk (𝟙 U.unop)))
          (e21.hom.val.app U (scalarExtensionSection β N U t x)) =
        s * t * β.hom.app U (f.app (op (Over.mk (𝟙 U.unop))) x))
    (h20 : ∀ (U : Cᵒᵖ) (s t : T.obj.obj U)
      (f : (homObj M (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))).val.obj U)
      (x : M.val.obj U),
      (D20.val.app U (scalarExtensionSection γ _ U s f)).app (op (Over.mk (𝟙 U.unop)))
          (e20.hom.val.app U (scalarExtensionSection γ M U t x)) =
        s * t * γ.hom.app U (f.app (op (Over.mk (𝟙 U.unop))) x))
    (U : Cᵒᵖ) (s : S.obj.obj U) (t : T.obj.obj U)
    (a : (homObj M (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))).val.obj U) :
    D21.val.app U (scalarExtensionSection β _ U t
      (D10.val.app U (scalarExtensionSection α _ U s a))) =
      D20.val.app U (scalarExtensionSection γ _ U (t * β.hom.app U s) a) := by
  subst hγ
  apply homObj_section_ext (α ≫ β) M P e20 U
  intro V i t' x
  rw [scalarExtension_hom_restrict, scalarExtension_hom_restrict, scalarExtension_hom_restrict,
    h20, ← he, h21, h10]
  have hn : T.obj.map i (β.hom.app U s) = β.hom.app V (S.obj.map i s) :=
    (ConcreteCategory.congr_hom (β.hom.naturality i) s).symm
  have hc (y : R.obj.obj V) : (α ≫ β).hom.app V y = β.hom.app V (α.hom.app V y) := rfl
  simp only [map_mul, hn, mul_one, hc]
  ring_nf

end Generic

section Concrete

attribute [local instance 5000] evaluationOverSheafify evaluationOverLocallyBijective

/-- A line of rank one is trivial on a covering family.
Source: Stacks 03EK (blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem line_cover (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1] :
    ∃ (I : Type (t + 1)) (V : I → X.ProEt),
      (AlgebraicGeometry.Scheme.ProEt.topology X).CoversTop V ∧
      ∀ i, Nonempty (L.over (V i) ≅ SheafOfModules.unit
        (((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology X)
          (forget₂ CommRingCat RingCat)).obj
            (completedIntegralCommRingSheafUnrestricted l E X)).over (V i))) := by
  classical
  obtain ⟨I, V, hV, e⟩ :=
    (SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free
      (M := L) (r := 1)).mp inferInstance
  exact ⟨I, V, hV, fun i ↦ ⟨(e i).some ≪≫ SheafOfModules.freeUniqueIso _⟩⟩

/-- The positive part of a normalized family is a normalized positive comparison.
Source: Stacks 03EK (blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem line_positive (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (N : integralTowerModules l F X) [N.IsFiniteLocallyFreeOfRank 1]
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N)
    {B : LineFamily l E X F ι L N} (hB : IsLineNormalized l E X F ι L N b B) :
    IsPositiveNormalized.{t + 1, t, u} (completedCoefficientMap l E F ι X) L N b
      (fun n ↦ (B (Int.ofNat n)).hom) := by
  have h : (fun n ↦ (B (Int.ofNat n)).hom) = fun n ↦ ((binary l E X F ι).power L n).hom ≫
      SheafOfModules.scalarTensorPowerMap.{t + 1, t, max u (t + 1)}
        (completedIntegralCommRingSheafUnrestricted l F X) b.hom n := funext hB.1
  rw [h]
  exact isPositiveNormalized_binary.{t + 1, t, u} _ L N b (binary l E X F ι)

end Concrete

/-- Normalized signed-power comparisons exist.
Source: Stacks 03EK, 0GMX; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: positive powers are the binary tensor comparison followed by the tensor power of
`b`. For a negative power, compose the dual scalar comparison, which is invertible on
lines, with precomposition by the inverse positive comparison. Evaluation cancels this
inverse and gives the pairing formula. -/
theorem line_exists (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (N : integralTowerModules l F X) [N.IsFiniteLocallyFreeOfRank 1]
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N) :
    ∃ B : LineFamily l E X F ι L N, IsLineNormalized l E X F ι L N b B := by
  obtain ⟨B, hB, hev, -⟩ := SheafOfModules.exists_signedLineComparison.{t + 1, t, u}
    (completedCoefficientMap l E F ι X) L N (line_cover l E X L) (line_cover l F X N) b
  have hpos := isPositiveNormalized_unique.{t + 1, t, u} (completedCoefficientMap l E F ι X) L N b
    (P := fun n ↦ (B (Int.ofNat n)).hom) ⟨hB.1, hB.2.1, hB.2.2.1⟩
    (isPositiveNormalized_binary.{t + 1, t, u} _ L N b (binary l E X F ι))
  refine ⟨B, fun n ↦ congrFun hpos n, fun n U s t f x ↦ ?_⟩
  have h := hev n U s t f x
  rw [mul_rotate] at h
  exact h

/-- Normalized signed-power comparisons are unique.
Source: Stacks 03EK, 03EO; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: positive powers are given by a formula. A negative comparison is determined by its
pairing with the positive comparison: sections of the scalar extension are locally sums
of pure tensors, the positive comparison is invertible, and a section of the dual sheaf is
determined by its values on all restrictions. -/
theorem line_unique (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (N : integralTowerModules l F X) [N.IsFiniteLocallyFreeOfRank 1]
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N)
    {B B' : LineFamily l E X F ι L N} (hB : IsLineNormalized l E X F ι L N b B)
    (hB' : IsLineNormalized l E X F ι L N b B') : B = B' := by
  funext m
  cases m with
  | ofNat n => exact Iso.ext ((hB.1 n).trans (hB'.1 n).symm)
  | negSucc n =>
    have hp : (B' (Int.ofNat (n + 1))).hom = (B (Int.ofNat (n + 1))).hom :=
      (hB'.1 (n + 1)).trans (hB.1 (n + 1)).symm
    refine Iso.ext (dualComparison_ext.{t + 1, t, u} (completedCoefficientMap l E F ι X) _ _
      (B (Int.ofNat (n + 1))) _ _ fun U s t f x ↦ ?_)
    have h' := hB'.2 n U s t f x
    rw [hp] at h'
    exact (hB.2 n U s t f x).trans h'.symm

variable (G : Type u) [Field G] [Algebra ℚ_[l] G] [FiniteDimensional ℚ_[l] G]
  (j : F →ₐ[ℚ_[l]] G)


/-- Completed coefficient maps compose along a tower of coefficient fields.
Source: Stacks 03EK (blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem completedCoefficientMap_comp :
    completedCoefficientMap l E F ι X ≫ completedCoefficientMap l F G j X =
      completedCoefficientMap l E G (j.comp ι) X := by
  apply (completedCoefficientMap_existsUnique l E G (j.comp ι) X).unique
  · intro n
    rw [Category.assoc, completedCoefficientMap_projection]
    rw [← Category.assoc, completedCoefficientMap_projection, Category.assoc]
    congr 1
    unfold integralScalarQuotientSheafMap
    erw [← Functor.map_comp]
    congr 1
    ext x
    obtain ⟨x⟩ := x
    induction x using Quotient.inductionOn' with
    | h x => rfl
  · simpa only [completedCoefficientMap] using
      (completedCoefficientMap_existsUnique l E G (j.comp ι) X).exists.choose_spec

/-- Normalized signed-power comparisons are compatible with a three-field tower.
Source: Stacks 03EK, 03EO; blueprint Proof (3), final sentence
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: for positive powers induct on the exponent, using the tower hypothesis on `b` and
the recursive binary formula. For negative powers both sides have the same pairing with
the positive comparisons, by the positive case, so they agree by uniqueness. -/
theorem line_tower (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (N : integralTowerModules l F X) [N.IsFiniteLocallyFreeOfRank 1]
    (P : integralTowerModules l G X) [P.IsFiniteLocallyFreeOfRank 1]
    (b10 : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N)
    (b21 : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l F G j X) N ≅ P)
    (b20 : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E G (j.comp ι) X) L ≅ P)
    (hb : ∀ (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
      (t : (completedIntegralCommRingSheafUnrestricted l G X).obj.obj U) (x : L.val.obj U),
      b21.hom.val.app U (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1),
          max u (t + 1)} (completedCoefficientMap l F G j X) N U t
          (b10.hom.val.app U (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1),
            max u (t + 1)} (completedCoefficientMap l E F ι X) L U s x))) =
        b20.hom.val.app U (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1),
          max u (t + 1)} (completedCoefficientMap l E G (j.comp ι) X) L U
          (t * (completedCoefficientMap l F G j X).hom.app U s) x))
    {B10 : LineFamily l E X F ι L N} {B21 : LineFamily l F X G j N P}
    {B20 : LineFamily l E X G (j.comp ι) L P}
    (h10 : IsLineNormalized l E X F ι L N b10 B10)
    (h21 : IsLineNormalized l F X G j N P b21 B21)
    (h20 : IsLineNormalized l E X G (j.comp ι) L P b20 B20)
    (m : ℤ) (U : X.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
    (t : (completedIntegralCommRingSheafUnrestricted l G X).obj.obj U)
    (a : (power l E X L m).val.obj U) :
    (B21 m).hom.val.app U (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1),
        max u (t + 1)} (completedCoefficientMap l F G j X) (power l F X N m) U t
        ((B10 m).hom.val.app U (SheafOfModules.scalarExtensionSection.{t + 1, t,
          max u (t + 1), max u (t + 1)} (completedCoefficientMap l E F ι X)
          (power l E X L m) U s a))) =
      (B20 m).hom.val.app U (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1),
        max u (t + 1)} (completedCoefficientMap l E G (j.comp ι) X) (power l E X L m) U
        (t * (completedCoefficientMap l F G j X).hom.app U s) a) := by
  have hγ := completedCoefficientMap_comp l E X F ι G j
  cases m with
  | ofNat n =>
    exact isPositiveNormalized_tower.{t + 1, t, u} _ _ _ hγ L N P b10 b21 b20 hb
      (line_positive l E X F ι L N b10 h10) (line_positive l F X G j N P b21 h21)
      (line_positive l E X G (j.comp ι) L P b20 h20) n U s t a
  | negSucc n =>
    have he (V : X.ProEtᵒᵖ)
        (t' : (completedIntegralCommRingSheafUnrestricted l G X).obj.obj V)
        (x : (power l E X L (Int.ofNat (n + 1))).val.obj V) :=
      isPositiveNormalized_tower.{t + 1, t, u} _ _ _ hγ L N P b10 b21 b20 hb
        (line_positive l E X F ι L N b10 h10) (line_positive l F X G j N P b21 h21)
        (line_positive l E X G (j.comp ι) L P b20 h20) (n + 1) V 1 t' x
    simp only [map_one, mul_one] at he
    exact dualComparison_tower.{t + 1, t, u} _ _ _ hγ _ _ _ (B10 (Int.ofNat (n + 1)))
      (B21 (Int.ofNat (n + 1))) (B20 (Int.ofNat (n + 1))) he _ _ _ (h10.2 n) (h21.2 n)
      (h20.2 n) U s t a

end CompletedLineTensor
end WeilConjectures
