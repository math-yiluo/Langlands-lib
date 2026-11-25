/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.CupProduct

public import WeilConjectures.SixFunctors.Etale.ConstantCohomologyRingChange
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantCohomologyDualityFrobenius

/-!
# The cup product on `Hⁿ(S_proét, ℤ/ℓᵐ)`

Let `S` be a quasi-compact quasi-separated scheme and `Λ = ℤ/ℓᵐ`. Through the comparison
`Hⁿ(S_proét, ℤ_ℓ/ℓᵐ) ≅ Extⁿ_Λ(Λ_S, Λ_S)` (`AlgebraicGeometry.ProEtale.extAddEquivFiniteAdicH`), the
Yoneda product of `Ext`-classes of étale sheaves of `Λ`-modules defines the cup product
`⌣ : Hⁱ(S, ℤ/ℓᵐ) × Hʲ(S, ℤ/ℓᵐ) ⟶ Hⁱ⁺ʲ(S, ℤ/ℓᵐ)`
(`AlgebraicGeometry.ProEtale.finiteAdicHCup`). It is the cup product
`AlgebraicGeometry.Etale.cupProduct` of the classes `Λ_S ⟶ Λ_S[n]` of `D(S_ét, Λ)`
(`AlgebraicGeometry.ProEtale.unitShiftAddEquivFiniteAdicH_cupProduct`), hence graded
commutative (`AlgebraicGeometry.ProEtale.finiteAdicHCup_comm`), compatible with the pullback
along an automorphism (`AlgebraicGeometry.ProEtale.finiteAdicHPullback_finiteAdicHCup`), and
compatible with the reductions `ℤ/ℓᵐ⁺¹ ⟶ ℤ/ℓᵐ` of the coefficients
(`AlgebraicGeometry.ProEtale.finiteAdicHTransition_finiteAdicHCup`), by the change of rings of
`WeilConjectures.SixFunctors.Etale.ConstantCohomologyRingChange`.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Etale

open CategoryTheory Limits Opposite

variable (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})

/-- The identification `forget(Λ_X) ≅ Λ_X` of abelian sheaves sends the generators of the constant
presheaf `Λ` to the generators of the constant presheaf `Λ`. -/
lemma toSheafify_comp_sheafForget₂ConstantRingIso_hom (U : X.Etaleᵒᵖ) :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
        ((toSheafify X.smallEtaleTopology
          ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of Λ Λ))).app U) ≫
      (sheafForget₂ConstantRingIso Λ X).hom.hom.app U =
    (toSheafify X.smallEtaleTopology
      ((Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of Λ))).app U := by
  let V := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let r : ℤ →+* Λ := Int.castRingHom Λ
  let R := ModuleCat.restrictScalars.{u + 1} r
  let T := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  have : R.IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{0, 0, u + 1} r).isLeftAdjoint
  have : V.IsLeftAdjoint := inferInstanceAs (R ⋙ T).IsLeftAdjoint
  have : X.smallEtaleTopology.PreservesSheafification V :=
    Sheaf.preservesSheafification_of_adjunction _ (Adjunction.ofIsLeftAdjoint V)
  have h := sheafComposeIso_inv_fac X.smallEtaleTopology V
    ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of Λ Λ))
  have hn := toSheafify_naturality X.smallEtaleTopology
    (Functor.constComp X.Etaleᵒᵖ (ModuleCat.of Λ Λ) V).hom
  have he := congrArg (fun k ↦ k ≫ sheafifyMap X.smallEtaleTopology
    (Functor.constComp X.Etaleᵒᵖ (ModuleCat.of Λ Λ) V).hom) h
  rw [Category.assoc, ← hn] at he
  have he' := congrArg (fun k ↦ k.app U) he
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.constComp_hom_app,
    Category.id_comp] at he'
  change V.map _ ≫ ((constantCommuteCompose X.smallEtaleTopology V).hom.app _).hom.app U = _
  rw [constantCommuteCompose_hom_app_hom]
  exact he'

/-- The global section of `Λ_X` corresponding to the identity is the generator `1`. -/
lemma constantRingHomEquiv_id :
    Sheaf.constantRingHomEquiv X.smallEtaleTopology (terminalEtaleIsTerminal X) Λ _ (𝟙 _) =
      ((toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of Λ Λ))).app (op (terminalEtale X))).hom
          (1 : Λ) := by
  rfl

/-- The global section of `ℤ_X` corresponding to the identity is the generator `1`. -/
lemma constantHomEquiv_id_eq :
    Sheaf.constantHomEquiv.{u + 1} (J := X.smallEtaleTopology) (terminalEtaleIsTerminal X) _ (𝟙 _) =
      ((toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
          (op (terminalEtale X))).hom (ULift.up.{u + 1} (1 : ℤ)) := by
  rfl

/-- The class `ℤ_X ⟶ Λ_X` of `1` is the constant sheaf map of `ℤ ⟶ Λ`. -/
lemma constantIntToRing_comp_sheafForget₂ConstantRingIso_hom :
    Sheaf.constantIntToRing X.smallEtaleTopology (terminalEtaleIsTerminal X) Λ ≫
        (sheafForget₂ConstantRingIso Λ X).hom =
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        (AddCommGrpCat.ofHom ((Int.castAddHom Λ).comp
          (AddEquiv.ulift : ULift.{u + 1} ℤ ≃+ ℤ).toAddMonoidHom)) := by
  apply (Sheaf.constantHomEquiv.{u + 1} (J := X.smallEtaleTopology) (terminalEtaleIsTerminal X)
    _).injective
  rw [Sheaf.constantHomEquiv_comp, Sheaf.constantIntToRing]
  erw [Equiv.apply_symm_apply, constantRingHomEquiv_id]
  conv_rhs => rw [← Category.id_comp ((constantSheaf _ _).map _), Sheaf.constantHomEquiv_comp,
    constantHomEquiv_id_eq]
  have hK := congrArg (fun k ↦ k.hom (1 : Λ))
    (toSheafify_comp_sheafForget₂ConstantRingIso_hom Λ X (op (terminalEtale X)))
  have hN := congrArg (fun k ↦ (k.app (op (terminalEtale X))).hom (ULift.up.{u + 1} (1 : ℤ)))
    (toSheafify_naturality X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).map
      (AddCommGrpCat.ofHom ((Int.castAddHom Λ).comp
          (AddEquiv.ulift : ULift.{u + 1} ℤ ≃+ ℤ).toAddMonoidHom))))
  dsimp at hK hN
  refine hK.trans (Eq.trans ?_ hN)
  exact congrArg _ (Int.cast_one (R := Λ)).symm

/-- If `ℤ ⟶ Λ` is surjective, the class `ℤ_X ⟶ Λ_X` of `1` is an epimorphism. -/
lemma epi_constantIntToRing (hΛ : Function.Surjective (Int.cast : ℤ → Λ)) :
    Epi (Sheaf.constantIntToRing X.smallEtaleTopology (terminalEtaleIsTerminal X) Λ) := by
  have h := constantIntToRing_comp_sheafForget₂ConstantRingIso_hom Λ X
  rw [← Iso.eq_comp_inv] at h
  rw [h]
  have : Epi (AddCommGrpCat.ofHom ((Int.castAddHom Λ).comp
          (AddEquiv.ulift : ULift.{u + 1} ℤ ≃+ ℤ).toAddMonoidHom)) := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro y
    obtain ⟨n, rfl⟩ := hΛ y
    exact ⟨ULift.up n, rfl⟩
  have := (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
    (terminalEtaleIsTerminal X)).isLeftAdjoint
  exact epi_comp _ _

/-- The map `Λ'_X ⟶ Λ_X` of underlying abelian sheaves induced by `φ : Λ' ⟶ Λ` is the constant
sheaf map of `φ`, if `ℤ ⟶ Λ'` is surjective. -/
lemma constantRingForgetMap_comp_sheafForget₂ConstantRingIso_hom {Λ' : Type (u + 1)}
    [CommRing Λ']
    (φ : Λ' →+* Λ) (hΛ' : Function.Surjective (Int.cast : ℤ → Λ')) :
    constantRingForgetMap φ X ≫ (sheafForget₂ConstantRingIso Λ X).hom =
      (sheafForget₂ConstantRingIso Λ' X).hom ≫
        (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
          (AddCommGrpCat.ofHom φ.toAddMonoidHom) := by
  have := epi_constantIntToRing Λ' X hΛ'
  rw [← cancel_epi (Sheaf.constantIntToRing X.smallEtaleTopology (terminalEtaleIsTerminal X) Λ'),
    reassoc_of% (constantIntToRing_comp_constantRingForgetMap φ X),
    constantIntToRing_comp_sheafForget₂ConstantRingIso_hom,
    reassoc_of% (constantIntToRing_comp_sheafForget₂ConstantRingIso_hom Λ' X),
    ← Functor.map_comp]
  congr 1
  ext x
  simp

end AlgebraicGeometry.Etale

open CategoryTheory Limits MonoidalCategory Abelian

namespace AlgebraicGeometry.ProEtale

open Scheme PadicInt

variable (l : ℕ) [Fact l.Prime] (m : ℕ) (S : Scheme.{u})

/-- The reduction `Hⁿ(S, ℤ/ℓᵐ⁺¹) ⟶ Hⁿ(S, ℤ/ℓᵐ)` of the coefficients. -/
noncomputable def finiteAdicHTransition (n : ℕ) :
    FiniteAdicH S l (m + 1) n →+ FiniteAdicH S l m n :=
  Sheaf.H.map (continuousSheafMap S
    (openAddSubgroupQuotientMap (powOpenAddSubgroup l) (powOpenAddSubgroup_succ_le l) m)) n

variable [CompactSpace S] [QuasiSeparatedSpace S]

/-- The **cup product** `Hⁱ(S, ℤ/ℓᵐ) × Hʲ(S, ℤ/ℓᵐ) ⟶ Hᵏ(S, ℤ/ℓᵐ)`, `i + j = k`: the Yoneda
product of `Ext`-classes of étale sheaves of `ℤ/ℓᵐ`-modules, read through
`AlgebraicGeometry.ProEtale.extAddEquivFiniteAdicH`. -/
noncomputable def finiteAdicHCup {i j k : ℕ} (h : i + j = k) :
    FiniteAdicH S l m i →+ FiniteAdicH S l m j →+ FiniteAdicH S l m k :=
  AddMonoidHom.mk' (fun x ↦ AddMonoidHom.mk' (fun y ↦ extAddEquivFiniteAdicH l m S k
      (((extAddEquivFiniteAdicH l m S i).symm x).comp ((extAddEquivFiniteAdicH l m S j).symm y)
        h)) fun y y' ↦ by simp [Ext.comp_add]) fun x x' ↦ by
    ext y
    simp [Ext.add_comp]

lemma finiteAdicHCup_apply {i j k : ℕ} (h : i + j = k) (x : FiniteAdicH S l m i)
    (y : FiniteAdicH S l m j) :
    finiteAdicHCup l m S h x y = extAddEquivFiniteAdicH l m S k
      (((extAddEquivFiniteAdicH l m S i).symm x).comp ((extAddEquivFiniteAdicH l m S j).symm y)
        h) :=
  rfl

omit [CompactSpace S] [QuasiSeparatedSpace S] in
/-- The comparison `Hom(Λ_S, Λ_S[n]) ≅ Extⁿ(Λ_S, Λ_S)` sends the cup product to the Yoneda
product. -/
lemma unitShiftAddEquivExt_cupProduct (Λ : Type (u + 1)) [CommRing Λ] {i j k : ℕ}
    (h : i + j = k)
    (x : 𝟙_ (Etale.DerivedCategoryModule Λ S) ⟶ (𝟙_ (Etale.DerivedCategoryModule Λ S))⟦(i : ℤ)⟧)
    (y : 𝟙_ (Etale.DerivedCategoryModule Λ S) ⟶ (𝟙_ (Etale.DerivedCategoryModule Λ S))⟦(j : ℤ)⟧) :
    Etale.unitShiftAddEquivExt Λ S k (Etale.cupProduct _ (i : ℤ) (j : ℤ) x y ≫
      eqToHom (by rw [← h, Nat.cast_add])) =
      (Etale.unitShiftAddEquivExt Λ S i x).comp (Etale.unitShiftAddEquivExt Λ S j y) h := by
  have hU := DerivedCategory.unitorsCommShift (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  ext
  rw [Ext.comp_hom, Etale.unitShiftAddEquivExt_hom, Etale.unitShiftAddEquivExt_hom,
    Etale.unitShiftAddEquivExt_hom, ShiftedHom.comp, Etale.cupProduct_eq_shiftProduct,
    shiftProduct_eq hU]
  simp only [Category.assoc, Functor.map_comp]
  rw [Iso.hom_inv_id_map_assoc]
  congr 2
  have h₂ := (shiftFunctorAdd' (DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (j : ℤ) i k (by lia)).inv.naturality (Etale.unitIsoSingleFunctorConstantSheaf Λ S).hom
  dsimp at h₂
  rw [h₂, reassoc_of% (shiftFunctorAdd'_inv_app_comp_eqToHom (j : ℤ) (i : ℤ) _ (k : ℤ)
    (add_comm _ _) (by lia))]

/-- The cup product of `Hⁿ(S, ℤ/ℓᵐ)` is the cup product `AlgebraicGeometry.Etale.cupProduct` of the
classes `Λ_S ⟶ Λ_S[n]` of `D(S_ét, Λ)`, `Λ = ℤ/ℓᵐ`. -/
theorem unitShiftAddEquivFiniteAdicH_cupProduct {i j k : ℕ} (h : i + j = k)
    (x : 𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m))) S) ⟶
      (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m))) S))⟦(i : ℤ)⟧)
    (y : 𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m))) S) ⟶
      (𝟙_ (Etale.DerivedCategoryModule (ULift.{u + 1} (ZMod (l ^ m))) S))⟦(j : ℤ)⟧) :
    unitShiftAddEquivFiniteAdicH l m S k
        (Etale.cupProduct _ (i : ℤ) (j : ℤ) x y ≫
          eqToHom (by rw [← h, Nat.cast_add])) =
      finiteAdicHCup l m S h (unitShiftAddEquivFiniteAdicH l m S i x)
        (unitShiftAddEquivFiniteAdicH l m S j y) := by
  rw [finiteAdicHCup_apply]
  simp only [unitShiftAddEquivFiniteAdicH, AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
  exact congrArg (extAddEquivFiniteAdicH l m S k) (unitShiftAddEquivExt_cupProduct S _ h x y)

omit [CompactSpace S] [QuasiSeparatedSpace S] in
/-- Graded commutativity of `AlgebraicGeometry.Etale.cupProduct`, with the degrees read in `ℕ`. -/
lemma cupProduct_comm_comp_eqToHom (Λ : Type (u + 1)) [CommRing Λ] {i j k : ℕ} (h : i + j = k)
    (x : 𝟙_ (Etale.DerivedCategoryModule Λ S) ⟶ (𝟙_ (Etale.DerivedCategoryModule Λ S))⟦(i : ℤ)⟧)
    (y : 𝟙_ (Etale.DerivedCategoryModule Λ S) ⟶ (𝟙_ (Etale.DerivedCategoryModule Λ S))⟦(j : ℤ)⟧) :
    Etale.cupProduct _ (j : ℤ) (i : ℤ) y x ≫
        eqToHom (by rw [← h, add_comm i j, Nat.cast_add] :
          (𝟙_ (Etale.DerivedCategoryModule Λ S))⟦(j : ℤ) + i⟧ =
            (𝟙_ (Etale.DerivedCategoryModule Λ S))⟦(k : ℤ)⟧) =
      (((i : ℤ) * j).negOnePow : ℤ) •
        (Etale.cupProduct _ (i : ℤ) (j : ℤ) x y ≫ eqToHom (by rw [← h, Nat.cast_add] :
          (𝟙_ (Etale.DerivedCategoryModule Λ S))⟦(i : ℤ) + j⟧ =
            (𝟙_ (Etale.DerivedCategoryModule Λ S))⟦(k : ℤ)⟧)) := by
  rw [Etale.cupProduct_comm, Units.smul_def, Preadditive.zsmul_comp, Category.assoc,
    eqToHom_trans]

/-- **Graded commutativity of the cup product**: `y ⌣ x = (-1)^{ij} x ⌣ y`. -/
theorem finiteAdicHCup_comm {i j k : ℕ} (h : i + j = k) (x : FiniteAdicH S l m i)
    (y : FiniteAdicH S l m j) :
    finiteAdicHCup l m S ((add_comm j i).trans h) y x =
      ((i : ℤ) * j).negOnePow • finiteAdicHCup l m S h x y := by
  obtain ⟨x, rfl⟩ := (unitShiftAddEquivFiniteAdicH l m S i).surjective x
  obtain ⟨y, rfl⟩ := (unitShiftAddEquivFiniteAdicH l m S j).surjective y
  refine (unitShiftAddEquivFiniteAdicH_cupProduct l m S _ y x).symm.trans ?_
  refine ((congrArg (unitShiftAddEquivFiniteAdicH l m S k)
    (cupProduct_comm_comp_eqToHom S _ h x y)).trans (map_zsmul _ _ _)).trans ?_
  exact congrArg ((((i : ℤ) * j).negOnePow : ℤ) • ·)
    (unitShiftAddEquivFiniteAdicH_cupProduct l m S h x y)

omit [CompactSpace S] [QuasiSeparatedSpace S] in
/-- The Frobenius operator of the shifted canonical Weil datum commutes with the identifications
`Λ_S[a] = Λ_S[b]`, `a = b`. -/
lemma frobeniusOperator_comp_eqToHom {Λ : Type (u + 1)} [CommRing Λ] (g : S ⟶ S) {a b : ℤ}
    (hab : a = b)
    (z : 𝟙_ (Etale.DerivedCategoryModule Λ S) ⟶ (𝟙_ (Etale.DerivedCategoryModule Λ S))⟦a⟧) :
    Etale.frobeniusOperator g
        (Etale.shiftWeilDatum g (Etale.leftDerivedUpperStarUnitIso _ g).hom b)
        (z ≫ eqToHom (by rw [hab])) =
      Etale.frobeniusOperator g
        (Etale.shiftWeilDatum g (Etale.leftDerivedUpperStarUnitIso _ g).hom a) z ≫
        eqToHom (by rw [hab]) := by
  subst hab
  simp only [eqToHom_refl, Category.comp_id]

omit [CompactSpace S] [QuasiSeparatedSpace S] in
/-- The Frobenius operator of the canonical Weil datum is multiplicative for the cup product, with
the degrees read in `ℕ`. -/
lemma frobeniusOperator_cupProduct_comp_eqToHom {Λ : Type (u + 1)} [CommRing Λ] (g : S ⟶ S)
    {i j k : ℕ} (h : i + j = k)
    (x : 𝟙_ (Etale.DerivedCategoryModule Λ S) ⟶ (𝟙_ (Etale.DerivedCategoryModule Λ S))⟦(i : ℤ)⟧)
    (y : 𝟙_ (Etale.DerivedCategoryModule Λ S) ⟶ (𝟙_ (Etale.DerivedCategoryModule Λ S))⟦(j : ℤ)⟧) :
    Etale.frobeniusOperator g
        (Etale.shiftWeilDatum g (Etale.leftDerivedUpperStarUnitIso _ g).hom (k : ℤ))
        (Etale.cupProduct _ (i : ℤ) (j : ℤ) x y ≫ eqToHom (by rw [← h, Nat.cast_add])) =
      Etale.cupProduct _ (i : ℤ) (j : ℤ)
        (Etale.frobeniusOperator g
          (Etale.shiftWeilDatum g (Etale.leftDerivedUpperStarUnitIso _ g).hom (i : ℤ)) x)
        (Etale.frobeniusOperator g
          (Etale.shiftWeilDatum g (Etale.leftDerivedUpperStarUnitIso _ g).hom (j : ℤ)) y) ≫
        eqToHom (by rw [← h, Nat.cast_add]) := by
  have hk : (i : ℤ) + j = k := by rw [← h, Nat.cast_add]
  rw [frobeniusOperator_comp_eqToHom S g hk, Etale.frobeniusOperator_cupProduct]

/-- The pullback along an automorphism `e` of a connected `S` is multiplicative for the cup
product. -/
theorem finiteAdicHPullback_finiteAdicHCup [ConnectedSpace S] (e : S ≅ S) {i j k : ℕ}
    (h : i + j = k) (x : FiniteAdicH S l m i) (y : FiniteAdicH S l m j) :
    finiteAdicHPullback e l m k (finiteAdicHCup l m S h x y) =
      finiteAdicHCup l m S h (finiteAdicHPullback e l m i x) (finiteAdicHPullback e l m j y) := by
  obtain ⟨x, rfl⟩ := (unitShiftAddEquivFiniteAdicH l m S i).surjective x
  obtain ⟨y, rfl⟩ := (unitShiftAddEquivFiniteAdicH l m S j).surjective y
  refine (congrArg (finiteAdicHPullback e l m k)
    (unitShiftAddEquivFiniteAdicH_cupProduct l m S h x y).symm).trans ?_
  refine (finiteAdicHPullback_unitShiftAddEquivFiniteAdicH l m S e k _).trans ?_
  refine (congrArg (unitShiftAddEquivFiniteAdicH l m S k)
    (frobeniusOperator_cupProduct_comp_eqToHom S e.hom h x y)).trans ?_
  refine (unitShiftAddEquivFiniteAdicH_cupProduct l m S h _ _).trans ?_
  exact congr_arg₂ (fun a b ↦ finiteAdicHCup l m S h a b)
    (finiteAdicHPullback_unitShiftAddEquivFiniteAdicH l m S e i x).symm
    (finiteAdicHPullback_unitShiftAddEquivFiniteAdicH l m S e j y).symm

/-- The reduction `ℤ/ℓᵐ⁺¹ ⟶ ℤ/ℓᵐ` of the coefficient rings. -/
noncomputable def zmodTransitionRingHom :
    ULift.{u + 1} (ZMod (l ^ (m + 1))) →+* ULift.{u + 1} (ZMod (l ^ m)) :=
  (ZMod.castHom (pow_dvd_pow l (Nat.le_succ m)) (ZMod (l ^ m))).ulift

/-- The cup product of classes of `Extⁿ_Λ(Λ_S, Λ_S)` is their Yoneda product. -/
lemma finiteAdicHCup_extAddEquivFiniteAdicH {i j k : ℕ} (h : i + j = k)
    (z : Ext (Sheaf.constantRing S.smallEtaleTopology (ULift.{u + 1} (ZMod (l ^ m))))
      (Sheaf.constantRing S.smallEtaleTopology (ULift.{u + 1} (ZMod (l ^ m)))) i)
    (z' : Ext (Sheaf.constantRing S.smallEtaleTopology (ULift.{u + 1} (ZMod (l ^ m))))
      (Sheaf.constantRing S.smallEtaleTopology (ULift.{u + 1} (ZMod (l ^ m)))) j) :
    finiteAdicHCup l m S h (extAddEquivFiniteAdicH l m S i z) (extAddEquivFiniteAdicH l m S j z') =
      extAddEquivFiniteAdicH l m S k (z.comp z' h) := by
  rw [finiteAdicHCup_apply, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]

/-- Pushing the change of rings `φ_*` along `ν^* ∘ forget`: `ψ ∘ φ_* z = z ∘ ψ` for the map
`ψ : Λ'_S ⟶ Λ_S` of constant sheaves. -/
lemma mapExactFunctor_extRingChange {Λ' Λ : Type (u + 1)} [CommRing Λ'] [CommRing Λ]
    (φ : Λ' →+* Λ) {n : ℕ}
    (z : Ext (Sheaf.constantRing S.smallEtaleTopology Λ')
      (Sheaf.constantRing S.smallEtaleTopology Λ') n) :
    (Ext.mk₀ ((Etale.sheafForget₂ Λ' S ⋙ comparisonUpperStar AddCommGrpCat.{u + 1} S).map
        (Etale.constantRingMap φ S))).comp
      ((Etale.extRingChange φ S n z).mapExactFunctor
        (Etale.sheafForget₂ Λ S ⋙ comparisonUpperStar AddCommGrpCat.{u + 1} S)) (zero_add n) =
      (z.mapExactFunctor
          (Etale.sheafForget₂ Λ' S ⋙ comparisonUpperStar AddCommGrpCat.{u + 1} S)).comp
        (Ext.mk₀ ((Etale.sheafForget₂ Λ' S ⋙ comparisonUpperStar AddCommGrpCat.{u + 1} S).map
          (Etale.constantRingMap φ S))) (add_zero n) := by
  have h := congrArg (fun e ↦ e.mapExactFunctor
    (Etale.sheafForget₂ Λ' S ⋙ comparisonUpperStar AddCommGrpCat.{u + 1} S))
    (Etale.mk₀_comp_mapExactFunctor_extRingChange φ S n z)
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.mapExactFunctor_mapExactFunctor] at h
  exact h

omit [Fact l.Prime] [CompactSpace S] [QuasiSeparatedSpace S] in
/-- The class `ℤ ⟶ ν^* Λ` of `1` is compatible with the reduction `ℤ/ℓᵐ⁺¹ ⟶ ℤ/ℓᵐ`. -/
lemma forgetComparisonUpperStarUnit_comp_map_constantRingMap :
    forgetComparisonUpperStarUnit l (m + 1) S ≫ (forgetComparisonUpperStar l (m + 1) S).map
      (Etale.constantRingMap (zmodTransitionRingHom l m) S) =
      forgetComparisonUpperStarUnit l m S := by
  have h := Etale.constantIntToRing_comp_constantRingForgetMap (zmodTransitionRingHom l m) S
  dsimp only [Etale.constantRingForgetMap, Etale.sheafRestrictScalarsCompSheafForget₂Iso,
    Iso.refl_hom, NatTrans.id_app] at h
  erw [Category.comp_id] at h
  rw [forgetComparisonUpperStarUnit, forgetComparisonUpperStarUnit, Category.assoc,
    Functor.comp_map, ← Functor.map_comp]
  erw [h]

omit [CompactSpace S] [QuasiSeparatedSpace S] in
/-- The isomorphism of the constant pro-étale sheaf with `U ↦ C(U, A)` is natural in `A`. -/
lemma constantSheaf_map_comp_constantSheafToContinuousSheaf {A B : Type} [TopologicalSpace A]
    [AddCommGroup A] [IsTopologicalAddGroup A] [TopologicalSpace B] [AddCommGroup B]
    [IsTopologicalAddGroup B] (f : ContinuousAddMonoidHom A B) :
    (constantSheaf (ProEt.topology S) AddCommGrpCat.{u + 1}).map (AddCommGrpCat.ofHom
        (AddEquiv.ulift.symm.toAddMonoidHom.comp
          ((f : A →+ B).comp AddEquiv.ulift.toAddMonoidHom))) ≫
      constantSheafToContinuousSheaf S B =
    constantSheafToContinuousSheaf S A ≫ continuousSheafMap S f := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ (continuousSheaf S B).property
  change toSheafify _ _ ≫ sheafifyMap _ _ ≫ _ = toSheafify _ _ ≫ _ ≫ _
  erw [← toSheafify_naturality_assoc, toSheafify_constantSheafToContinuousSheaf,
    ← Category.assoc, toSheafify_constantSheafToContinuousSheaf]
  rfl

/-- `ℤ/ℓᵐ ≅ ℤ_ℓ/ℓᵐ` sends the class of an integer to its class. -/
lemma zmodAddEquivQuotientPowOpenAddSubgroup_intCast (n : ℤ) :
    zmodAddEquivQuotientPowOpenAddSubgroup l m (n : ZMod (l ^ m)) =
      QuotientAddGroup.mk (n : ℤ_[l]) := by
  rw [← AddEquiv.eq_symm_apply, zmodAddEquivQuotientPowOpenAddSubgroup, AddEquiv.symm_trans_apply,
    AddEquiv.symm_symm]
  exact (map_intCast (PadicInt.toZModPow m) n).symm

/-- The identifications `ℤ/ℓᵐ ≅ ℤ_ℓ/ℓᵐ` are compatible with the reductions. -/
lemma zmodAddEquivQuotientPowOpenAddSubgroup_castHom (x : ZMod (l ^ (m + 1))) :
    zmodAddEquivQuotientPowOpenAddSubgroup l m
        (ZMod.castHom (pow_dvd_pow l (Nat.le_succ m)) (ZMod (l ^ m)) x) =
      openAddSubgroupQuotientMap (PadicInt.powOpenAddSubgroup l)
        (PadicInt.powOpenAddSubgroup_succ_le l) m
        (zmodAddEquivQuotientPowOpenAddSubgroup l (m + 1) x) := by
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
  rw [map_intCast, zmodAddEquivQuotientPowOpenAddSubgroup_intCast,
    zmodAddEquivQuotientPowOpenAddSubgroup_intCast]
  rfl

omit [CompactSpace S] [QuasiSeparatedSpace S] in
/-- The identifications `ν^* Λ_S ≅ C(-, ℤ_ℓ/ℓᵐ)` are compatible with the reductions. -/
lemma forgetComparisonUpperStarConstantRingIso_transition :
    (forgetComparisonUpperStar l (m + 1) S).map
        (Etale.constantRingMap (zmodTransitionRingHom l m) S) ≫
      (forgetComparisonUpperStarConstantRingIso l m S).hom =
    (forgetComparisonUpperStarConstantRingIso l (m + 1) S).hom ≫ continuousSheafMap S
      (openAddSubgroupQuotientMap (PadicInt.powOpenAddSubgroup l)
        (PadicInt.powOpenAddSubgroup_succ_le l) m) := by
  have h1 : (forgetComparisonUpperStar l (m + 1) S).map
      (Etale.constantRingMap (zmodTransitionRingHom l m) S) =
      (comparisonUpperStar AddCommGrpCat.{u + 1} S).map
        (Etale.constantRingForgetMap (zmodTransitionRingHom l m) S) := by
    simp only [Etale.constantRingForgetMap, Etale.sheafRestrictScalarsCompSheafForget₂Iso,
      Iso.refl_hom, NatTrans.id_app]
    erw [Category.comp_id]
    rfl
  rw [h1]
  simp only [forgetComparisonUpperStarConstantRingIso, sheafForget₂ConstantRingIsoQuotient,
    Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc,
    constantSheafIsoContinuousSheaf, asIso_hom]
  rw [← constantSheaf_map_comp_constantSheafToContinuousSheaf, ← NatTrans.naturality_assoc,
    Functor.comp_map, ← Functor.map_comp_assoc]
  erw [← Functor.map_comp_assoc]
  congr 2
  rw [reassoc_of% (Etale.constantRingForgetMap_comp_sheafForget₂ConstantRingIso_hom _ S _
    (surjective_intCast_ulift_zmod l (m + 1))), Category.assoc, ← Functor.map_comp,
    ← Functor.map_comp]
  congr 2
  ext x
  exact zmodAddEquivQuotientPowOpenAddSubgroup_castHom l m x.down

/-- The comparison `Extⁿ_Λ(Λ_S, Λ_S) ≅ Hⁿ(S_proét, ℤ_ℓ/ℓᵐ)` intertwines the change of rings
`ℤ/ℓᵐ⁺¹ ⟶ ℤ/ℓᵐ` with the reduction of the coefficients. -/
lemma extAddEquivFiniteAdicH_extRingChange (n : ℕ)
    (z : Ext (Sheaf.constantRing S.smallEtaleTopology (ULift.{u + 1} (ZMod (l ^ (m + 1)))))
      (Sheaf.constantRing S.smallEtaleTopology (ULift.{u + 1} (ZMod (l ^ (m + 1))))) n) :
    extAddEquivFiniteAdicH l m S n (Etale.extRingChange (zmodTransitionRingHom l m) S n z) =
      finiteAdicHTransition l m S n (extAddEquivFiniteAdicH l (m + 1) S n z) := by
  have key : Ext.mk₀CompMk₀ (forgetComparisonUpperStarUnit l m S)
      ((Etale.extRingChange (zmodTransitionRingHom l m) S n z).mapExactFunctor
        (forgetComparisonUpperStar l m S)) (forgetComparisonUpperStarConstantRingIso l m S).hom =
      (Ext.mk₀CompMk₀ (forgetComparisonUpperStarUnit l (m + 1) S)
        (z.mapExactFunctor (forgetComparisonUpperStar l (m + 1) S))
        (forgetComparisonUpperStarConstantRingIso l (m + 1) S).hom).comp
          (Ext.mk₀ (continuousSheafMap S (openAddSubgroupQuotientMap (powOpenAddSubgroup l)
            (powOpenAddSubgroup_succ_le l) m))) (add_zero n) := by
    rw [Ext.mk₀CompMk₀_comp_mk₀, ← forgetComparisonUpperStarConstantRingIso_transition,
      ← forgetComparisonUpperStarUnit_comp_map_constantRingMap]
    refine (Ext.mk₀_comp_mk₀CompMk₀ _ _ _ _).symm.trans ?_
    refine congrArg (fun e ↦ (Ext.mk₀ (forgetComparisonUpperStarUnit l (m + 1) S)).comp e
      (zero_add n)) ?_
    refine (Ext.mk₀_comp_comp_mk₀ _ _ _).symm.trans ?_
    refine (congrArg (fun e ↦ e.comp (Ext.mk₀ (forgetComparisonUpperStarConstantRingIso l m S).hom)
      (add_zero n)) (mapExactFunctor_extRingChange S (zmodTransitionRingHom l m) z)).trans ?_
    refine (Ext.comp_assoc_of_third_deg_zero _ _ _ _).trans ?_
    exact congrArg (fun e ↦ Ext.comp _ e (add_zero n)) (Ext.mk₀_comp_mk₀ _ _)
  exact (extAddEquivFiniteAdicH_apply l m S n _).trans (key.trans (congrArg
    (finiteAdicHTransition l m S n) (extAddEquivFiniteAdicH_apply l (m + 1) S n z)).symm)

/-- The reduction `ℤ/ℓᵐ⁺¹ ⟶ ℤ/ℓᵐ` of the coefficients is multiplicative for the cup product. -/
theorem finiteAdicHTransition_finiteAdicHCup {i j k : ℕ} (h : i + j = k)
    (x : FiniteAdicH S l (m + 1) i) (y : FiniteAdicH S l (m + 1) j) :
    finiteAdicHTransition l m S k (finiteAdicHCup l (m + 1) S h x y) =
      finiteAdicHCup l m S h (finiteAdicHTransition l m S i x)
        (finiteAdicHTransition l m S j y) := by
  obtain ⟨z, rfl⟩ := (extAddEquivFiniteAdicH l (m + 1) S i).surjective x
  obtain ⟨z', rfl⟩ := (extAddEquivFiniteAdicH l (m + 1) S j).surjective y
  refine (congrArg (finiteAdicHTransition l m S k)
    (finiteAdicHCup_extAddEquivFiniteAdicH l (m + 1) S h z z')).trans ?_
  refine (extAddEquivFiniteAdicH_extRingChange l m S k _).symm.trans ?_
  refine (congrArg (extAddEquivFiniteAdicH l m S k)
    (Etale.extRingChange_comp _ S h z z')).trans ?_
  refine (finiteAdicHCup_extAddEquivFiniteAdicH l m S h _ _).symm.trans ?_
  exact congr_arg₂ (fun a b ↦ finiteAdicHCup l m S h a b)
    (extAddEquivFiniteAdicH_extRingChange l m S i z)
    (extAddEquivFiniteAdicH_extRingChange l m S j z')

omit [CompactSpace S] [QuasiSeparatedSpace S] in
/-- `c ∈ ℤ_ℓ` acts on `Hⁿ(S, ℤ/ℓᵐ)` as the natural number `PadicInt.appr c m`. -/
lemma smul_finiteAdicH_eq_nsmul {n : ℕ} (c : ℤ_[l]) (x : FiniteAdicH S l m n) :
    c • x = c.appr m • x := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec m c)
  have hc : c = (c.appr m : ℤ_[l]) + a * (l : ℤ_[l]) ^ m := by rw [ha]; ring
  rw [congrArg (· • x) hc, add_smul, mul_smul, pow_smul_finiteAdicH, smul_zero, add_zero,
    Nat.cast_smul_eq_nsmul ℤ_[l]]

/-- The cup product is `ℤ_ℓ`-linear in the first variable. -/
theorem finiteAdicHCup_smul_left {i j k : ℕ} (h : i + j = k) (c : ℤ_[l])
    (x : FiniteAdicH S l m i) (y : FiniteAdicH S l m j) :
    finiteAdicHCup l m S h (c • x) y = c • finiteAdicHCup l m S h x y := by
  rw [smul_finiteAdicH_eq_nsmul, smul_finiteAdicH_eq_nsmul, map_nsmul, AddMonoidHom.nsmul_apply]

/-- The cup product is `ℤ_ℓ`-linear in the second variable. -/
theorem finiteAdicHCup_smul_right {i j k : ℕ} (h : i + j = k) (c : ℤ_[l])
    (x : FiniteAdicH S l m i) (y : FiniteAdicH S l m j) :
    finiteAdicHCup l m S h x (c • y) = c • finiteAdicHCup l m S h x y := by
  rw [smul_finiteAdicH_eq_nsmul, smul_finiteAdicH_eq_nsmul, map_nsmul]

end AlgebraicGeometry.ProEtale
