/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.FreePresentation
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleExtendScalarsBaseChange
public import WeilConjectures.SixFunctors.ProEtale.Adic.RightDerivedLowerStarFilteredColimit

/-!
# Extension of scalars `ℚ̄_ℓ ⊗_{ℤ_ℓ} -` as a colimit of copies of the module

Choose a basis `B` of `ℚ̄_ℓ` over `ℚ_ℓ`. For a `ℤ_ℓ,X`-module `M` on `X_proét` there is a natural
morphism of abelian sheaves
```
κ_M : ⨁_{b ∈ B} colim (M --ℓ--> M --ℓ--> M --ℓ--> ⋯) ⟶ ℚ̄_ℓ ⊗_{ℤ_ℓ} M
```
(`AlgebraicGeometry.ProEtale.rationalizationComparison`), sending the `n`-th copy of `M` in the
summand `b` to `ℚ̄_ℓ ⊗ M` by `m ↦ (b / ℓⁿ) ⊗ m`. Since `ℚ̄_ℓ,X = ⨁_B ℚ_ℓ,X` and
`ℚ_ℓ,X = colim (ℤ_ℓ,X --ℓ--> ℤ_ℓ,X --ℓ--> ⋯)` as `ℤ_ℓ,X`-modules, `κ_M` is an isomorphism
(*the rationalization formula*); this is not proved here, and is a hypothesis
(`[IsIso (rationalizationComparison X l)]`) of the results below.

Granting the rationalization formula on `X` and on `Y`, and the continuity of higher direct
images along a quasi-compact quasi-separated `f : X ⟶ Y`
(`WeilConjectures.SixFunctors.ProEtale.Adic.RightDerivedLowerStarFilteredColimit`), the
three hypotheses of
`WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleExtendScalarsBaseChange` hold:

* extension of scalars is exact
  (`AlgebraicGeometry.ProEtale.preservesFiniteLimits_adicSheafExtendScalars`);
* for every injective `ℤ_ℓ,X`-module `I`, `ℚ̄_ℓ ⊗ I` is `f_*`-acyclic
  (`AlgebraicGeometry.ProEtale.rightAcyclic_lowerStar_toAb_adicSheafExtendScalars_obj`);
* the comparison `ℚ̄_ℓ ⊗ f_* M ⟶ f_* (ℚ̄_ℓ ⊗ M)` is an isomorphism
  (`AlgebraicGeometry.ProEtale.isIso_adicSheafExtendScalarsPushforwardComparison`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory

variable {C : Type*} [Category* C] [Preadditive C] (l : ℕ)

/-- The tower `A --ℓ--> A --ℓ--> A --ℓ--> ⋯` of multiplications by `ℓ`, functorially in `A`. -/
noncomputable def ellMulTower : C ⥤ ℕ ⥤ C :=
  (Functor.ofSequence fun _ ↦ (l : ℤ) • 𝟙 (𝟭 C)).flip

@[simp]
lemma ellMulTower_obj_obj (A : C) (n : ℕ) : ((ellMulTower l).obj A).obj n = A :=
  rfl

@[simp]
lemma ellMulTower_obj_map_succ (A : C) (n : ℕ) :
    ((ellMulTower l).obj A).map (homOfLE (Nat.le_add_right n 1)) = (l : ℤ) • 𝟙 A := by
  simp [ellMulTower]

@[simp]
lemma ellMulTower_map_app {A A' : C} (g : A ⟶ A') (n : ℕ) :
    ((ellMulTower l).map g).app n = g :=
  rfl

/-- The functor `A ↦ colim (A --ℓ--> A --ℓ--> ⋯)`, which inverts `ℓ`. -/
noncomputable abbrev ellRat [HasColimitsOfShape ℕ C] : C ⥤ C :=
  ellMulTower l ⋙ colim

/-- The functor `A ↦ ⨁_B A`. -/
noncomputable abbrev sigmaConstFunctor (B : Type) [HasColimitsOfShape (Discrete B) C] : C ⥤ C :=
  Functor.const (Discrete B) ⋙ colim

/-- The tower of multiplications by `ℓ` is exact in the object, being the identity in each
degree. -/
instance preservesFiniteLimits_ellMulTower : PreservesFiniteLimits (ellMulTower l : C ⥤ ℕ ⥤ C) :=
  preservesFiniteLimits_of_evaluation _ fun n ↦
    preservesFiniteLimits_of_natIso (NatIso.ofComponents (fun A ↦ Iso.refl A) (by simp) :
      𝟭 C ≅ ellMulTower l ⋙ (evaluation ℕ C).obj n)

variable {l} in
/-- An additive functor commutes with the towers of multiplications by `ℓ`. -/
noncomputable def ellMulTowerCompIso {D : Type*} [Category* D] [Preadditive D] (G : C ⥤ D)
    [G.Additive] (A : C) : (ellMulTower l).obj (G.obj A) ≅ (ellMulTower l).obj A ⋙ G where
  hom := NatTrans.ofSequence (fun _ ↦ 𝟙 _) fun n ↦ by simp
  inv := NatTrans.ofSequence (fun _ ↦ 𝟙 _) fun n ↦ by simp
  hom_inv_id := by ext; simp
  inv_hom_id := by ext; simp

@[simp]
lemma ellMulTowerCompIso_hom_app {D : Type*} [Category* D] [Preadditive D] (G : C ⥤ D)
    [G.Additive] (A : C) (n : ℕ) : (ellMulTowerCompIso (l := l) G A).hom.app n = 𝟙 _ :=
  rfl

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

variable (l : ℕ) [Fact l.Prime]

/-- A basis of `ℚ̄_ℓ` over `ℚ_ℓ`, indexed by a subset of `ℚ̄_ℓ`. -/
noncomputable abbrev padicAlgClBasisIndex : Type :=
  Module.Basis.ofVectorSpaceIndex ℚ_[l] (PadicAlgCl l)

/-- Multiplication by a scalar `v ∈ ℚ̄_ℓ` on the underlying abelian sheaf of an `ℓ`-adic sheaf. -/
noncomputable def adicScalarMul {X : Scheme.{u}} (P : AdicSheaf l X) (v : PadicAlgCl l) :
    (AdicSheaf.toAb l X).obj P ⟶ (AdicSheaf.toAb l X).obj P :=
  (weilCoefficientsForgetAb l X).map ((ULift.up v : ULift.{u + 1} (PadicAlgCl l)) • 𝟙 P.X)

/-- Multiplication by scalars commutes with morphisms of `ℓ`-adic sheaves. -/
@[reassoc]
lemma adicScalarMul_naturality {X : Scheme.{u}} {P Q : AdicSheaf l X} (g : P ⟶ Q)
    (v : PadicAlgCl l) :
    adicScalarMul l P v ≫ (AdicSheaf.toAb l X).map g =
      (AdicSheaf.toAb l X).map g ≫ adicScalarMul l Q v := by
  simp only [adicScalarMul, AdicSheaf.toAb, Functor.comp_map, ← Functor.map_comp]
  congr 1
  rw [Linear.smul_comp, Linear.comp_smul]
  erw [Category.id_comp]

/-- Multiplication by scalars is additive in the scalar. -/
lemma zsmul_adicScalarMul {X : Scheme.{u}} (P : AdicSheaf l X) (v : PadicAlgCl l) (k : ℤ) :
    k • adicScalarMul l P v = adicScalarMul l P (k • v) := by
  rw [adicScalarMul, adicScalarMul, ← Functor.map_zsmul,
    ← Int.cast_smul_eq_zsmul (ULift.{u + 1} (PadicAlgCl l)), smul_smul]
  congr 2
  ext
  simp

/-- The pushforward of the multiplication by a scalar is the multiplication by this scalar on the
pushforward. -/
lemma lowerStar_map_adicScalarMul {X Y : Scheme.{u}} (f : X ⟶ Y) (P : AdicSheaf l X)
    (v : PadicAlgCl l) :
    ((f)_*[Ab.{u + 1}]).map (adicScalarMul l P v) = adicScalarMul l ((f)_*ᵃ[l].obj P) v :=
  rfl

/-- The isomorphism `res (f_* F) ≅ f_* (res F)` is the identity on underlying abelian sheaves. -/
lemma adicLowerStarRestrictPadicIntPushforwardIso_inv_app_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : AdicSheaf l X) :
    ((adicLowerStarRestrictPadicIntPushforwardIso l f).inv.app P).hom = 𝟙 _ := by
  simp only [Functor.comp_obj, adicLowerStarRestrictPadicIntPushforwardIso, Iso.refl_hom,
    NatTrans.id_app, adicLowerStarCompRestrictPadicIntPushforwardIso, Functor.mapModComapIso,
    Functor.isoWhiskerLeft_trans, Functor.mapModCompIso, Iso.trans_assoc, Mod.comapCongr,
    restrictPadicIntCompPadicIntModPushforwardIso, Iso.trans_symm, Iso.symm_symm_eq,
    Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerLeft_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Category.assoc, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.whiskerRight_app,
    NatIso.ofComponents_hom_app, Functor.comp_map, NatIso.ofComponents_inv_app,
    Category.comp_id, Category.id_comp, Mod.comp_hom', Mod.id_hom', Mod.comap_map_hom,
    Mod.isoMk_hom_hom, asIso_hom, Mod.comapComp_inv_app_hom, Mod.isoMk_inv_hom, Iso.refl_inv,
    Mod.comapComp_hom_app_hom, asIso_inv]
  erw [IsIso.inv_id]
  rfl

/-! ### The rationalization formula -/

section Model

variable (X : Scheme.{u})

/-- The functor `M ↦ ⨁_{b ∈ B} colim (M --ℓ--> M --ℓ--> ⋯)` from `ℤ_ℓ,X`-modules to abelian
sheaves, for the basis `B` of `ℚ̄_ℓ` over `ℚ_ℓ`: a model of `ℚ̄_ℓ ⊗_{ℤ_ℓ} M`. -/
noncomputable def rationalizationModel :
    Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l) ⥤
      Sheaf (ProEt.topology X) Ab.{u + 1} :=
  Mod.forget _ ⋙ ellRat l ⋙ sigmaConstFunctor (padicAlgClBasisIndex l)

/-- The unit `M ⟶ ℚ̄_ℓ ⊗_{ℤ_ℓ} M`, as a morphism of abelian sheaves. -/
noncomputable def adicSheafExtendScalarsUnitAb
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l)) :
    (Mod.forget _).obj M ⟶ (AdicSheaf.toAb l X).obj ((adicSheafExtendScalars X l).obj M) :=
  (Mod.forget _).map ((adicSheafExtendScalarsRestrictAdjunction X l).unit.app M)

/-- The map `m ↦ (b / ℓⁿ) ⊗ m` from `M` to `ℚ̄_ℓ ⊗_{ℤ_ℓ} M`. -/
noncomputable def rationalizationComparisonι
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l))
    (b : padicAlgClBasisIndex l) (n : ℕ) :
    (Mod.forget _).obj M ⟶ (AdicSheaf.toAb l X).obj ((adicSheafExtendScalars X l).obj M) :=
  adicSheafExtendScalarsUnitAb l X M ≫
    adicScalarMul l ((adicSheafExtendScalars X l).obj M)
      ((b : PadicAlgCl l) / (l : PadicAlgCl l) ^ n)

lemma zsmul_rationalizationComparisonι
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l))
    (b : padicAlgClBasisIndex l) (n : ℕ) :
    (l : ℤ) • rationalizationComparisonι l X M b (n + 1) =
      rationalizationComparisonι l X M b n := by
  rw [rationalizationComparisonι, rationalizationComparisonι, ← Preadditive.comp_zsmul,
    zsmul_adicScalarMul]
  congr 2
  have : (l : PadicAlgCl l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  rw [zsmul_eq_mul, Int.cast_natCast, pow_succ]
  field_simp

lemma zsmul_comp_rationalizationComparisonι
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l))
    (b : padicAlgClBasisIndex l) (n : ℕ) :
    ((l : ℤ) • 𝟙 ((Mod.forget _).obj M)) ≫ rationalizationComparisonι l X M b (n + 1) =
      rationalizationComparisonι l X M b n := by
  rw [Preadditive.zsmul_comp]
  erw [Category.id_comp]
  exact zsmul_rationalizationComparisonι l X M b n

/-- The cocone `(m ↦ (b / ℓⁿ) ⊗ m)ₙ` over `M --ℓ--> M --ℓ--> ⋯`. -/
noncomputable def rationalizationComparisonCocone
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l))
    (b : padicAlgClBasisIndex l) :
    Cocone ((ellMulTower l).obj ((Mod.forget _).obj M)) :=
  Cocone.mk ((AdicSheaf.toAb l X).obj ((adicSheafExtendScalars X l).obj M))
    (NatTrans.ofSequence (fun n ↦ rationalizationComparisonι l X M b n) fun n ↦ by
      rw [ellMulTower_obj_map_succ, zsmul_comp_rationalizationComparisonι]
      exact (Category.comp_id _).symm)

/-- The comparison `⨁_{b ∈ B} colim (M --ℓ--> M --ℓ--> ⋯) ⟶ ℚ̄_ℓ ⊗_{ℤ_ℓ} M`. -/
noncomputable def rationalizationComparisonApp
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l)) :
    (rationalizationModel l X).obj M ⟶
      (AdicSheaf.toAb l X).obj ((adicSheafExtendScalars X l).obj M) :=
  colimit.desc _ (Cocone.mk _ (Discrete.natTrans fun b ↦
    colimit.desc _ (rationalizationComparisonCocone l X M b.as)))

@[reassoc (attr := simp)]
lemma ι_ι_rationalizationComparisonApp
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l))
    (b : padicAlgClBasisIndex l) (n : ℕ) :
    colimit.ι ((ellMulTower l).obj ((Mod.forget _).obj M)) n ≫
      colimit.ι ((Functor.const (Discrete (padicAlgClBasisIndex l))).obj
        (colimit ((ellMulTower l).obj ((Mod.forget _).obj M)))) ⟨b⟩ ≫
        rationalizationComparisonApp l X M = rationalizationComparisonι l X M b n := by
  simp [rationalizationComparisonApp, rationalizationComparisonCocone]

/-- Morphisms out of `⨁_{b ∈ B} colim (M --ℓ--> M --ℓ--> ⋯)` are determined by their
restrictions to the copies of `M`. -/
lemma rationalizationModel_hom_ext
    {M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l)}
    {Z : Sheaf (ProEt.topology X) Ab.{u + 1}} {g h : (rationalizationModel l X).obj M ⟶ Z}
    (H : ∀ (b : padicAlgClBasisIndex l) (n : ℕ),
      colimit.ι ((ellMulTower l).obj ((Mod.forget _).obj M)) n ≫
        colimit.ι ((Functor.const (Discrete (padicAlgClBasisIndex l))).obj
          (colimit ((ellMulTower l).obj ((Mod.forget _).obj M)))) ⟨b⟩ ≫ g =
      colimit.ι ((ellMulTower l).obj ((Mod.forget _).obj M)) n ≫
        colimit.ι ((Functor.const (Discrete (padicAlgClBasisIndex l))).obj
          (colimit ((ellMulTower l).obj ((Mod.forget _).obj M)))) ⟨b⟩ ≫ h) : g = h :=
  colimit.hom_ext fun j ↦ colimit.hom_ext fun n ↦ H j.as n

@[reassoc (attr := simp)]
lemma ι_ι_rationalizationModel_map
    {M M' : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l)} (g : M ⟶ M')
    (b : padicAlgClBasisIndex l) (n : ℕ) :
    colimit.ι ((ellMulTower l).obj ((Mod.forget _).obj M)) n ≫
      colimit.ι ((Functor.const (Discrete (padicAlgClBasisIndex l))).obj
        (colimit ((ellMulTower l).obj ((Mod.forget _).obj M)))) ⟨b⟩ ≫
        (rationalizationModel l X).map g =
      g.hom ≫ colimit.ι ((ellMulTower l).obj ((Mod.forget _).obj M')) n ≫
        colimit.ι ((Functor.const (Discrete (padicAlgClBasisIndex l))).obj
          (colimit ((ellMulTower l).obj ((Mod.forget _).obj M')))) ⟨b⟩ := by
  simp [rationalizationModel]

/-- The naturality of the unit `M ⟶ ℚ̄_ℓ ⊗_{ℤ_ℓ} M` on underlying abelian sheaves. -/
@[reassoc]
lemma adicSheafExtendScalarsUnitAb_naturality
    {M M' : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l)} (g : M ⟶ M') :
    g.hom ≫ adicSheafExtendScalarsUnitAb l X M' =
      adicSheafExtendScalarsUnitAb l X M ≫
        (AdicSheaf.toAb l X).map ((adicSheafExtendScalars X l).map g) := by
  have h := congrArg (Mod.forget _).map
    ((adicSheafExtendScalarsRestrictAdjunction X l).unit.naturality g)
  simp only [Functor.map_comp] at h
  exact h

/-- **The rationalization comparison** `⨁_{b ∈ B} colim (M --ℓ--> M --ℓ--> ⋯) ⟶ ℚ̄_ℓ ⊗_{ℤ_ℓ} M`,
natural in the `ℤ_ℓ,X`-module `M`, sending the `n`-th copy of `M` in the summand `b` to
`ℚ̄_ℓ ⊗ M` by `m ↦ (b / ℓⁿ) ⊗ m`. It is an isomorphism (*the rationalization formula*), since
`ℚ̄_ℓ,X = ⨁_B ℚ_ℓ,X` and `ℚ_ℓ,X = colim (ℤ_ℓ,X --ℓ--> ℤ_ℓ,X --ℓ--> ⋯)` as `ℤ_ℓ,X`-modules; this
is not proved here. -/
noncomputable def rationalizationComparison :
    rationalizationModel l X ⟶ adicSheafExtendScalars X l ⋙ AdicSheaf.toAb l X where
  app M := rationalizationComparisonApp l X M
  naturality M M' g := by
    refine rationalizationModel_hom_ext l X fun b n ↦ ?_
    rw [ι_ι_rationalizationModel_map_assoc, ι_ι_rationalizationComparisonApp,
      ι_ι_rationalizationComparisonApp_assoc, rationalizationComparisonι,
      rationalizationComparisonι, Category.assoc, adicSheafExtendScalarsUnitAb_naturality_assoc,
      Functor.comp_map, adicScalarMul_naturality]
    rfl

@[simp]
lemma rationalizationComparison_app
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l)) :
    (rationalizationComparison l X).app M = rationalizationComparisonApp l X M :=
  rfl

/-- **Exactness of extension of scalars**: granting the rationalization formula,
`ℚ̄_ℓ ⊗_{ℤ_ℓ} -` is exact, `⨁_{b ∈ B} colim (M --ℓ--> M --ℓ--> ⋯)` being exact in `M` (filtered
colimits and direct sums of abelian sheaves are exact). -/
theorem preservesFiniteLimits_adicSheafExtendScalars [IsIso (rationalizationComparison l X)] :
    PreservesFiniteLimits (adicSheafExtendScalars X l) := by
  have := AB5OfSize_of_univLE.{0, 0} (Sheaf (ProEt.topology X) Ab.{u + 1})
  have : HasFiniteBiproducts (Sheaf (ProEt.topology X) Ab.{u + 1}) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have : HasExactColimitsOfShape (Discrete (padicAlgClBasisIndex l))
      (Sheaf (ProEt.topology X) Ab.{u + 1}) :=
    hasExactColimitsOfShape_discrete_of_hasExactColimitsOfShape_finset_discrete _ _
  have : PreservesFiniteLimits (rationalizationModel l X) := by
    dsimp only [rationalizationModel]
    infer_instance
  have : PreservesFiniteLimits (adicSheafExtendScalars X l ⋙ AdicSheaf.toAb l X) :=
    preservesFiniteLimits_of_natIso (asIso (rationalizationComparison l X))
  have : PreservesFiniteLimits (weilCoefficientsForgetAb l X) :=
    have : PreservesLimitsOfSize.{0, 0} (weilCoefficientsForgetAb l X) :=
      (weilCoefficientsFreeAdjunction X l).rightAdjoint_preservesLimits
    PreservesLimitsOfSize.preservesFiniteLimits _
  exact preservesFiniteLimits_of_reflects_of_preserves _ (AdicSheaf.toAb l X)

/-- **`ℚ̄_ℓ ⊗ I` is `f_*`-acyclic for injective `I`**: granting the rationalization formula,
`ℚ̄_ℓ ⊗ I = ⨁_{b ∈ B} colim (I --ℓ--> I --ℓ--> ⋯)` is a direct sum of filtered colimits of
injective abelian sheaves, which are `f_*`-acyclic for `f` quasi-compact and quasi-separated. -/
theorem rightAcyclic_lowerStar_toAb_adicSheafExtendScalars_obj {Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [IsIso (rationalizationComparison l X)]
    (I : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l)) [Injective I] :
    ((f)_*[Ab.{u + 1}]).rightAcyclic
      ((AdicSheaf.toAb l X).obj ((adicSheafExtendScalars X l).obj I)) := by
  refine ObjectProperty.prop_of_iso _ (asIso ((rationalizationComparison l X).app I)) ?_
  refine rightAcyclic_lowerStar_of_isColimit_discrete f (colimit.isColimit _) fun _ ↦ ?_
  refine rightAcyclic_lowerStar_of_isColimit f (colimit.isColimit _) fun _ ↦ ?_
  exact Functor.rightAcyclic_of_injective ((Mod.forget _).obj I)

/-- `M ↦ ⨁_{b ∈ B} colim (M --ℓ--> M --ℓ--> ⋯)` is right exact. -/
instance preservesFiniteColimits_rationalizationModel :
    PreservesFiniteColimits (rationalizationModel l X) := by
  have : PreservesFiniteColimits (ellMulTower l : Sheaf (ProEt.topology X) Ab.{u + 1} ⥤ _) :=
    preservesFiniteColimits_of_evaluation _ fun n ↦
      preservesFiniteColimits_of_natIso (NatIso.ofComponents (fun A ↦ Iso.refl A) (by simp) :
        𝟭 _ ≅ ellMulTower l ⋙ (evaluation ℕ _).obj n)
  dsimp only [rationalizationModel]
  infer_instance

/-- `M ↦ ℚ̄_ℓ ⊗_{ℤ_ℓ} M`, on underlying abelian sheaves, is right exact. -/
instance preservesFiniteColimits_adicSheafExtendScalars_comp_toAb :
    PreservesFiniteColimits (adicSheafExtendScalars X l ⋙ AdicSheaf.toAb l X) := by
  have : PreservesFiniteColimits (weilCoefficientsForgetAb l X) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  dsimp only [AdicSheaf.toAb]
  infer_instance

/-- **Reduction of the rationalization formula to free modules**: the rationalization comparison
is an isomorphism as soon as it is one on the free `ℤ_ℓ,X`-modules `ℤ_ℓ,X ⊗ Z`, both sides being
right exact in `M`. -/
theorem isIso_rationalizationComparison_of_free
    (h : ∀ Z : Sheaf (ProEt.topology X) Ab.{u + 1},
      IsIso ((rationalizationComparison l X).app ((Mod.free (padicIntAbSheaf X l)).obj Z))) :
    IsIso (rationalizationComparison l X) := by
  rw [NatTrans.isIso_iff_isIso_app]
  exact Mod.isIso_app_of_isIso_app_free _ _ h

end Model

/-! ### Extension of scalars commutes with the pushforward -/

section Pushforward

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

/-- For `f` quasi-compact and quasi-separated, `f_*` commutes with `A ↦ colim (A --ℓ--> ⋯)`. -/
noncomputable def lowerStarEllRatIso (A : Sheaf (ProEt.topology X) Ab.{u + 1}) :
    colimit ((ellMulTower l).obj ((f)_*[Ab.{u + 1}].obj A)) ≅
      (f)_*[Ab.{u + 1}].obj (colimit ((ellMulTower l).obj A)) :=
  have := preservesColimitsOfShape_lowerStar f ℕ
  HasColimit.isoOfNatIso (ellMulTowerCompIso _ A) ≪≫ (preservesColimitIso _ _).symm

omit [Fact l.Prime] in
@[reassoc (attr := simp)]
lemma ι_lowerStarEllRatIso_hom (A : Sheaf (ProEt.topology X) Ab.{u + 1}) (n : ℕ) :
    colimit.ι ((ellMulTower l).obj ((f)_*[Ab.{u + 1}].obj A)) n ≫
      (lowerStarEllRatIso l f A).hom =
      (f)_*[Ab.{u + 1}].map (colimit.ι ((ellMulTower l).obj A) n) := by
  simp [lowerStarEllRatIso]

/-- `ι_lowerStarEllRatIso_hom` for the underlying abelian sheaf of a `ℤ_ℓ`-module. -/
@[reassoc]
lemma ι_lowerStarEllRatIso_hom'
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l)) (n : ℕ) :
    colimit.ι ((ellMulTower l).obj ((Mod.forget _).obj ((padicIntModPushforward l f).obj M))) n ≫
      (lowerStarEllRatIso l f ((Mod.forget _).obj M)).hom =
      (f)_*[Ab.{u + 1}].map (colimit.ι ((ellMulTower l).obj ((Mod.forget _).obj M)) n) :=
  ι_lowerStarEllRatIso_hom l f _ n

/-- For `f` quasi-compact and quasi-separated, `f_*` commutes with `A ↦ ⨁_B A`. -/
noncomputable def lowerStarSigmaConstIso (A : Sheaf (ProEt.topology X) Ab.{u + 1}) :
    colimit ((Functor.const (Discrete (padicAlgClBasisIndex l))).obj ((f)_*[Ab.{u + 1}].obj A)) ≅
      (f)_*[Ab.{u + 1}].obj
        (colimit ((Functor.const (Discrete (padicAlgClBasisIndex l))).obj A)) :=
  have := preservesColimitsOfShape_discrete_lowerStar f (padicAlgClBasisIndex l)
  HasColimit.isoOfNatIso (Functor.constComp _ _ _).symm ≪≫ (preservesColimitIso _ _).symm

@[reassoc (attr := simp)]
lemma ι_lowerStarSigmaConstIso_hom (A : Sheaf (ProEt.topology X) Ab.{u + 1})
    (b : Discrete (padicAlgClBasisIndex l)) :
    colimit.ι ((Functor.const (Discrete (padicAlgClBasisIndex l))).obj
      ((f)_*[Ab.{u + 1}].obj A)) b ≫ (lowerStarSigmaConstIso l f A).hom =
      (f)_*[Ab.{u + 1}].map
        (colimit.ι ((Functor.const (Discrete (padicAlgClBasisIndex l))).obj A) b) := by
  simp [lowerStarSigmaConstIso]

/-- For `f` quasi-compact and quasi-separated, `f_*` commutes with
`M ↦ ⨁_{b ∈ B} colim (M --ℓ--> M --ℓ--> ⋯)`. -/
noncomputable def lowerStarRationalizationModelIso
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l)) :
    (rationalizationModel l Y).obj ((padicIntModPushforward l f).obj M) ≅
      (f)_*[Ab.{u + 1}].obj ((rationalizationModel l X).obj M) :=
  (sigmaConstFunctor (padicAlgClBasisIndex l)).mapIso
      (lowerStarEllRatIso l f ((Mod.forget _).obj M)) ≪≫
    lowerStarSigmaConstIso l f (colimit ((ellMulTower l).obj ((Mod.forget _).obj M)))

@[reassoc (attr := simp)]
lemma ι_ι_lowerStarRationalizationModelIso_hom
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l))
    (b : padicAlgClBasisIndex l) (n : ℕ) :
    colimit.ι ((ellMulTower l).obj ((Mod.forget _).obj ((padicIntModPushforward l f).obj M))) n ≫
      colimit.ι ((Functor.const (Discrete (padicAlgClBasisIndex l))).obj
        (colimit ((ellMulTower l).obj
          ((Mod.forget _).obj ((padicIntModPushforward l f).obj M))))) ⟨b⟩ ≫
        (lowerStarRationalizationModelIso l f M).hom =
      (f)_*[Ab.{u + 1}].map (colimit.ι ((ellMulTower l).obj ((Mod.forget _).obj M)) n ≫
        colimit.ι ((Functor.const (Discrete (padicAlgClBasisIndex l))).obj
          (colimit ((ellMulTower l).obj ((Mod.forget _).obj M)))) ⟨b⟩) := by
  simp only [lowerStarRationalizationModelIso, Iso.trans_hom, Functor.mapIso_hom,
    Functor.comp_map, colim_map, ι_colimMap_assoc, Functor.const_map_app,
    ι_lowerStarSigmaConstIso_hom]
  rw [ι_lowerStarEllRatIso_hom'_assoc, Functor.map_comp]

omit [QuasiCompact f] [QuasiSeparated f] in
/-- The unit and the comparison `ℚ̄_ℓ ⊗ f_* M ⟶ f_* (ℚ̄_ℓ ⊗ M)`: on underlying abelian sheaves,
`f_* M ⟶ ℚ̄_ℓ ⊗ f_* M ⟶ f_* (ℚ̄_ℓ ⊗ M)` is the pushforward of the unit `M ⟶ ℚ̄_ℓ ⊗ M`. -/
lemma adicSheafExtendScalarsUnitAb_comp_toAb_map_pushforwardComparison
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l)) :
    adicSheafExtendScalarsUnitAb l Y ((padicIntModPushforward l f).obj M) ≫
      (AdicSheaf.toAb l Y).map ((adicSheafExtendScalarsPushforwardComparison l f).app M) =
      (f)_*[Ab.{u + 1}].map (adicSheafExtendScalarsUnitAb l X M) := by
  have h := congrArg (fun φ ↦ φ.hom) (unit_mateEquiv_symm
    (adicSheafExtendScalarsRestrictAdjunction X l) (adicSheafExtendScalarsRestrictAdjunction Y l)
    (TwoSquare.mk _ _ _ _ (adicLowerStarRestrictPadicIntPushforwardIso l f).inv) M)
  simp only [Mod.comp_hom'] at h
  erw [adicLowerStarRestrictPadicIntPushforwardIso_inv_app_hom, Category.comp_id] at h
  exact h.symm

/-- The comparison `ℚ̄_ℓ ⊗ f_* M ⟶ f_* (ℚ̄_ℓ ⊗ M)` in terms of the rationalization comparisons. -/
lemma rationalizationComparison_app_comp_toAb_map_pushforwardComparison
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l)) :
    (rationalizationComparison l Y).app ((padicIntModPushforward l f).obj M) ≫
      (AdicSheaf.toAb l Y).map ((adicSheafExtendScalarsPushforwardComparison l f).app M) =
      (lowerStarRationalizationModelIso l f M).hom ≫
        (f)_*[Ab.{u + 1}].map ((rationalizationComparison l X).app M) := by
  refine rationalizationModel_hom_ext l Y fun b n ↦ ?_
  simp only [rationalizationComparison_app, ι_ι_rationalizationComparisonApp_assoc,
    ι_ι_lowerStarRationalizationModelIso_hom_assoc, ← Functor.map_comp, Category.assoc,
    ι_ι_rationalizationComparisonApp, rationalizationComparisonι]
  rw [adicScalarMul_naturality, ← Category.assoc,
    adicSheafExtendScalarsUnitAb_comp_toAb_map_pushforwardComparison, Functor.map_comp,
    lowerStar_map_adicScalarMul]
  rfl

/-- **Extension of scalars commutes with the pushforward**: granting the rationalization formula
on `X` and on `Y`, the comparison `ℚ̄_ℓ ⊗ f_* M ⟶ f_* (ℚ̄_ℓ ⊗ M)` is an isomorphism for `f`
quasi-compact and quasi-separated, `f_*` commuting with direct sums and filtered colimits. -/
theorem isIso_adicSheafExtendScalarsPushforwardComparison [IsIso (rationalizationComparison l X)]
    [IsIso (rationalizationComparison l Y)] :
    IsIso (adicSheafExtendScalarsPushforwardComparison l f) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  rw [← isIso_iff_of_reflects_iso _ (AdicSheaf.toAb l Y)]
  have h : (AdicSheaf.toAb l Y).map ((adicSheafExtendScalarsPushforwardComparison l f).app M) =
      inv ((rationalizationComparison l Y).app ((padicIntModPushforward l f).obj M)) ≫
        (lowerStarRationalizationModelIso l f M).hom ≫
          (f)_*[Ab.{u + 1}].map ((rationalizationComparison l X).app M) := by
    rw [← rationalizationComparison_app_comp_toAb_map_pushforwardComparison, IsIso.inv_hom_id_assoc]
  rw [h]
  infer_instance

end Pushforward

/-! ### Higher direct images of extensions of scalars -/

section RightDerived

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
  [IsIso (rationalizationComparison l X)] [IsIso (rationalizationComparison l Y)]

/-- **`ℚ̄_ℓ ⊗ Hᵠ(Rf_* M[0]) ≅ Hᵠ(Rf_* (ℚ̄_ℓ ⊗ M)[0])`** for `f` quasi-compact and
quasi-separated, granting the rationalization formula on `X` and on `Y`: an isomorphism of
`ℓ`-adic sheaves, the left hand side computed for `ℤ_ℓ`-modules. -/
noncomputable def adicSheafExtendScalarsHomologyRightDerivedIsoOfRationalization
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l)) (q : ℕ) :
    (adicSheafExtendScalars Y l).obj ((DerivedCategory.homologyFunctor _ q).obj
        ((padicIntModPushforward l f).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj M))) ≅
      (DerivedCategory.homologyFunctor _ q).obj ((f)_*ᵃ[l].rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj ((adicSheafExtendScalars X l).obj M))) :=
  have := preservesFiniteLimits_adicSheafExtendScalars l X
  have := preservesFiniteLimits_adicSheafExtendScalars l Y
  have := isIso_adicSheafExtendScalarsPushforwardComparison l f
  adicSheafExtendScalarsHomologyRightDerivedIso l f
    (fun I _ ↦ rightAcyclic_lowerStar_toAb_adicSheafExtendScalars_obj l X f I) M q

/-- **Lisse direct images from the integral ones** for `f` quasi-compact and quasi-separated,
granting the rationalization formula on `X` and on `Y`: if `ℚ̄_ℓ ⊗ Hᵠ(Rf_* M[0])` is lisse, the
right hand side computed for `ℤ_ℓ`-modules, then so is `Hᵠ(Rf_* (ℚ̄_ℓ ⊗ M)[0])`. -/
theorem isAdicLisseSheaf_homology_rightDerivedFunctor_adicLowerStar_of_rationalization
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l)) (q : ℕ)
    (hM : IsAdicLisseSheaf ((adicSheafExtendScalars Y l).obj
      ((DerivedCategory.homologyFunctor _ q).obj
        ((padicIntModPushforward l f).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj M))))) :
    IsAdicLisseSheaf ((DerivedCategory.homologyFunctor _ q).obj ((f)_*ᵃ[l].rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj ((adicSheafExtendScalars X l).obj M)))) :=
  hM.of_iso (adicSheafExtendScalarsHomologyRightDerivedIsoOfRationalization l f M q)

end RightDerived

end AlgebraicGeometry.ProEtale
