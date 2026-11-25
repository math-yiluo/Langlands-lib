/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Coef.CoefFiniteHomSiteDescentData
public import WeilConjectures.SixFunctors.SheafRestrictionTowerData.StrictRestrictionTower
import all WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientSiteScalarArrow

/-! # Composition of the normalized ordinary coefficient restriction comparisons

Source: blueprint finite Hom proof, successive quotient comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u a b r w
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem intrinsic_comp_inv_sections
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{r}} (f : R ⟶ S) (g : S ⟶ T) (q : R ⟶ T)
    (e : f ≫ g = q) (M : SheafOfModules.{w} T) (U : Cᵒᵖ) (x : M.val.obj U) :
    (((normalizedDVRRestrictionComp f g q e).inv.app M).val.app U) x = x := by
  cases e
  rfl

private theorem etale_comp_sections
    {C : Type a} [Category.{b} C] (J : GrothendieckTopology C)
    {A B D : Type r} [CommRing A] [CommRing B] [CommRing D]
    (φ : A →+* B) (ψ : B →+* D) (χ : A →+* D) (e : χ = ψ.comp φ)
    (M : Sheaf J (ModuleCat.{r} D)) (U : Cᵒᵖ) (x : M.obj.obj U) :
    ((Sheaf.restrictScalarsCompIso J φ ψ χ e).hom.app M).hom.app U x = x := by
  rfl

variable (X : Scheme.{u}) (A B C : Type u)
  [CommRing A] [CommRing B] [CommRing C]

private theorem nuSection_naturalityGeneral
    {M N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))}
    (f : M ⟶ N) (U : X.Etale) (x : M.obj.obj (op U)) :
    ((ProEtale.finiteCoefficientIntrinsicComparison X A).map f).val.app
        (op (X.toProEt.obj U)) (finiteHomNuSectionGeneral X A M U x) =
      finiteHomNuSectionGeneral X A N U (f.hom.app (op U) x) := by
  let R := ProEtale.finiteCoefficientIntrinsicScalarMap X A
  let P := ProEtale.finiteCoefficientModulePresheaf X.ProEt (ULift.{u + 1, u} A)
  let V := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X
  have hs := (PresheafOfModules.sheafificationAdjunction R).unit.naturality
    (P.map ((V.map f).hom))
  have hc := (ProEtale.comparisonAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).unit.naturality f
  have hs' := congrArg (fun z ↦ z.app (op (X.toProEt.obj U))
    (((ProEtale.comparisonAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).unit.app M).hom.app (op U) x)) hs
  have hc' := congrArg (fun z ↦ z.hom.app (op U) x) hc
  let η := (ProEtale.comparisonAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).unit
  let ι := (PresheafOfModules.sheafificationAdjunction R).unit
  change (η.app N).hom.app (op U) (f.hom.app (op U) x) =
    (V.map f).hom.app (op (X.toProEt.obj U)) ((η.app M).hom.app (op U) x) at hc'
  change (ι.app (P.obj (V.obj N).obj)).app (op (X.toProEt.obj U))
      ((V.map f).hom.app (op (X.toProEt.obj U)) ((η.app M).hom.app (op U) x)) =
    ((ProEtale.finiteCoefficientIntrinsicComparison X A).map f).val.app
      (op (X.toProEt.obj U)) (finiteHomNuSectionGeneral X A M U x) at hs'
  rw [← hc'] at hs'
  exact hs'.symm

variable
  (φ : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B)
  (ψ : ULift.{u + 1, u} B →+* ULift.{u + 1, u} C)
  (χ : ULift.{u + 1, u} A →+* ULift.{u + 1, u} C) (e : χ = ψ.comp φ)
  (f : (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (proEtaleConstantRing X A) ⟶
    (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (proEtaleConstantRing X B))
  (g : (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (proEtaleConstantRing X B) ⟶
    (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (proEtaleConstantRing X C))
  (q : (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (proEtaleConstantRing X A) ⟶
    (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (proEtaleConstantRing X C)) (eq : f ≫ g = q)

private theorem restriction_sectionsGeneral
    (σ : ProEtale.finiteCoefficientIntrinsicComparison X B ⋙ SheafOfModules.restrictScalars f ≅
      Sheaf.restrictScalars X.smallEtaleTopology φ ⋙
        ProEtale.finiteCoefficientIntrinsicComparison X A)
    (hσ : FiniteHomNuRestrictionNormalizationGeneral X A B φ f σ)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))
    (U : X.Etale) (x : M.obj.obj (op U)) :
    (σ.hom.app M).val.app (op (X.toProEt.obj U))
        (finiteHomNuSectionGeneral X B M U x) =
      finiteHomNuSectionGeneral X A
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj M) U x := by
  obtain ⟨z, y, hz, hy, he⟩ := hσ M U x
  have hy' : y = x := eq_of_heq hy
  have hz' : z = finiteHomNuSectionGeneral X B M U x := eq_of_heq hz
  exact (congrArg (fun t ↦ (σ.hom.app M).val.app (op (X.toProEt.obj U)) t) hz').symm.trans
    ((eq_of_heq he).trans (congrArg (fun t ↦ finiteHomNuSectionGeneral X A
      ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj M) U t) hy'))

section
attribute [local irreducible] ProEtale.finiteCoefficientIntrinsicComparison
  finiteHomNuSectionGeneral

private def restrictionCompositeGeneral
    (σ : ProEtale.finiteCoefficientIntrinsicComparison X B ⋙ SheafOfModules.restrictScalars f ≅
      Sheaf.restrictScalars X.smallEtaleTopology φ ⋙
        ProEtale.finiteCoefficientIntrinsicComparison X A)
    (τ : ProEtale.finiteCoefficientIntrinsicComparison X C ⋙ SheafOfModules.restrictScalars g ≅
      Sheaf.restrictScalars X.smallEtaleTopology ψ ⋙
        ProEtale.finiteCoefficientIntrinsicComparison X B) :
    ProEtale.finiteCoefficientIntrinsicComparison X C ⋙ SheafOfModules.restrictScalars q ≅
      Sheaf.restrictScalars X.smallEtaleTopology χ ⋙
        ProEtale.finiteCoefficientIntrinsicComparison X A :=
  Functor.isoWhiskerLeft _ (normalizedDVRRestrictionComp f g q eq).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight τ _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ σ ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Sheaf.restrictScalarsCompIso X.smallEtaleTopology φ ψ χ e) _

private theorem restrictionComposite_normalizedGeneral
    (σ : ProEtale.finiteCoefficientIntrinsicComparison X B ⋙ SheafOfModules.restrictScalars f ≅
      Sheaf.restrictScalars X.smallEtaleTopology φ ⋙
        ProEtale.finiteCoefficientIntrinsicComparison X A)
    (τ : ProEtale.finiteCoefficientIntrinsicComparison X C ⋙ SheafOfModules.restrictScalars g ≅
      Sheaf.restrictScalars X.smallEtaleTopology ψ ⋙
        ProEtale.finiteCoefficientIntrinsicComparison X B)
    (hσ : FiniteHomNuRestrictionNormalizationGeneral X A B φ f σ)
    (hτ : FiniteHomNuRestrictionNormalizationGeneral X B C ψ g τ) :
    FiniteHomNuRestrictionNormalizationGeneral X A C χ q
      (restrictionCompositeGeneral X A B C φ ψ χ e f g q eq σ τ) := by
  intro M U x
  refine ⟨finiteHomNuSectionGeneral X C M U x, x, HEq.rfl, HEq.rfl, ?_⟩
  apply heq_of_eq
  dsimp only [restrictionCompositeGeneral, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app]
  simp only [Category.id_comp]
  change ((ProEtale.finiteCoefficientIntrinsicComparison X A).map
      ((Sheaf.restrictScalarsCompIso X.smallEtaleTopology φ ψ χ e).hom.app M)).val.app
    (op (X.toProEt.obj U))
    ((σ.hom.app _).val.app (op (X.toProEt.obj U))
      ((τ.hom.app M).val.app (op (X.toProEt.obj U))
        (((normalizedDVRRestrictionComp f g q eq).inv.app
          ((ProEtale.finiteCoefficientIntrinsicComparison X C).obj M)).val.app
          (op (X.toProEt.obj U)) (finiteHomNuSectionGeneral X C M U x)))) = _
  rw [intrinsic_comp_inv_sections]
  rw [restriction_sectionsGeneral X B C ψ g τ hτ]
  erw [restriction_sectionsGeneral X A B φ f σ hσ]
  have hn := nuSection_naturalityGeneral X A
    ((Sheaf.restrictScalarsCompIso X.smallEtaleTopology φ ψ χ e).hom.app M) U x
  have he := etale_comp_sections X.smallEtaleTopology φ ψ χ e M (op U) x
  exact hn.trans (congrArg (fun z ↦ finiteHomNuSectionGeneral X A
    ((Sheaf.restrictScalars X.smallEtaleTopology χ).obj M) U z) he)

private theorem restriction_chainGeneral
    (σ : ProEtale.finiteCoefficientIntrinsicComparison X B ⋙ SheafOfModules.restrictScalars f ≅
      Sheaf.restrictScalars X.smallEtaleTopology φ ⋙
        ProEtale.finiteCoefficientIntrinsicComparison X A)
    (τ : ProEtale.finiteCoefficientIntrinsicComparison X C ⋙ SheafOfModules.restrictScalars g ≅
      Sheaf.restrictScalars X.smallEtaleTopology ψ ⋙
        ProEtale.finiteCoefficientIntrinsicComparison X B)
    (ρ : ProEtale.finiteCoefficientIntrinsicComparison X C ⋙ SheafOfModules.restrictScalars q ≅
      Sheaf.restrictScalars X.smallEtaleTopology χ ⋙
        ProEtale.finiteCoefficientIntrinsicComparison X A)
    (hσ : FiniteHomNuRestrictionNormalizationGeneral X A B φ f σ)
    (hτ : FiniteHomNuRestrictionNormalizationGeneral X B C ψ g τ)
    (hρ : FiniteHomNuRestrictionNormalizationGeneral X A C χ q ρ)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} C))) :
    (ProEtale.finiteCoefficientIntrinsicComparison X A).map
        ((Sheaf.restrictScalarsCompIso X.smallEtaleTopology φ ψ χ e).inv.app M) ≫
      σ.inv.app ((Sheaf.restrictScalars X.smallEtaleTopology ψ).obj M) ≫
      (SheafOfModules.restrictScalars f).map (τ.inv.app M) =
    ρ.inv.app M ≫ (normalizedDVRRestrictionComp f g q eq).inv.app
      ((ProEtale.finiteCoefficientIntrinsicComparison X C).obj M) := by
  have hi := finiteHomRestriction_uniqueGeneral X A C χ q
    (restrictionCompositeGeneral X A B C φ ψ χ e f g q eq σ τ) ρ
    (restrictionComposite_normalizedGeneral X A B C φ ψ χ e f g q eq σ τ hσ hτ) hρ
  have he := congrArg (fun i ↦ i.inv.app M) hi
  have h := congrArg (fun t ↦ t ≫ (normalizedDVRRestrictionComp f g q eq).inv.app
    ((ProEtale.finiteCoefficientIntrinsicComparison X C).obj M)) he
  simp only [restrictionCompositeGeneral, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.assoc, Iso.hom_inv_id_app] at h
  erw [Category.comp_id] at h
  exact h

end

attribute [local irreducible] ProEtale.finiteCoefficientIntrinsicComparison

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]

/-- The normalized ordinary restriction comparison respects successive coefficient quotients.
Source: blueprint finite Hom proof, successive quotient paragraph
(blueprint: lem-coef-finite-hom-ordinary-restriction-chain).
Proof: form the composite using the two restriction comparisons and the identity-on-sections
restriction associators. Naturality of the comparison unit and module-sheafification unit
shows that the composite fixes each local generator. Uniqueness of the normalized comparison
identifies it with the comparison of the composite quotient. Invert that equality and cancel
the intrinsic restriction associator. The calculation permits identity and repeated levels. -/
theorem finiteHomOrdinaryRestriction_chain {n m r : ℕ} (h : m ≤ n) (k : r ≤ m)
    (M : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (r + 1))))) :
    (finiteHomNuOrdinary l E X n).map ((Sheaf.restrictScalarsCompIso X.smallEtaleTopology
        (finiteHomQuotient l E h)
        (finiteHomQuotient l E k) (finiteHomQuotient l E (k.trans h))
        (finiteHomQuotient_comp l E h k)).inv.app M) ≫
      (finiteHomNuRestriction l E X h).inv.app
        ((Sheaf.restrictScalars X.smallEtaleTopology (finiteHomQuotient l E k)).obj M) ≫
      (normalizedDVRModuleRes l E X h).map ((finiteHomNuRestriction l E X k).inv.app M) =
    (finiteHomNuRestriction l E X (k.trans h)).inv.app M ≫
      (normalizedDVRRestrictionComp (normalizedDVRQuotient l E X h)
        (normalizedDVRQuotient l E X k) (normalizedDVRQuotient l E X (k.trans h))
        ((integralCoefficientSheafSystem l E X).map_comp
          (homOfLE h).op (homOfLE k).op).symm).inv.app ((finiteHomNuOrdinary l E X r).obj M) := by
  have hσ := (finiteHomNuRestriction_existsUnique l E X h).choose_spec.1
  have hτ := (finiteHomNuRestriction_existsUnique l E X k).choose_spec.1
  have hρ := (finiteHomNuRestriction_existsUnique l E X (k.trans h)).choose_spec.1
  change FiniteHomNuRestrictionNormalization l E X h (finiteHomNuRestriction l E X h) at hσ
  change FiniteHomNuRestrictionNormalization l E X k (finiteHomNuRestriction l E X k) at hτ
  change FiniteHomNuRestrictionNormalization l E X (k.trans h)
    (finiteHomNuRestriction l E X (k.trans h)) at hρ
  exact restriction_chainGeneral X
    (Padic.coefficientExtensionRing l E (n + 1))
    (Padic.coefficientExtensionRing l E (m + 1))
    (Padic.coefficientExtensionRing l E (r + 1))
    (finiteHomQuotient l E h) (finiteHomQuotient l E k)
    (finiteHomQuotient l E (k.trans h)) (finiteHomQuotient_comp l E h k)
    (normalizedDVRQuotient l E X h) (normalizedDVRQuotient l E X k)
    (normalizedDVRQuotient l E X (k.trans h))
    ((integralCoefficientSheafSystem l E X).map_comp (homOfLE h).op (homOfLE k).op).symm
    (finiteHomNuRestriction l E X h) (finiteHomNuRestriction l E X k)
    (finiteHomNuRestriction l E X (k.trans h))
    hσ hτ hρ M

end WeilConjectures
