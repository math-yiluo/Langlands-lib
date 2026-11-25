/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.Curry
public import WeilConjectures.SixFunctors.ProEtale.Adic.GeometricFrobeniusMate
public import WeilConjectures.WeilSheaf.Fourier
public import WeilConjectures.WeilSheaf.IhomLisse.UpperStarComparison
public import WeilConjectures.WeilSheaf.StalkTensor
public import WeilConjectures.WeilSheaf.StalkUpperStar
public import WeilConjectures.WeilSheaf.UpperStarConstant

/-!
# Pullback of the internal hom out of a lisse Weil sheaf

For a morphism `φ : X ⟶ Y` of `k₀`-schemes, the pullback `φ̄^*` along its base change to the
geometric fibres is strong monoidal, and the exchange isomorphism `φ̄^* ⋙ Fr_X^* ≅ Fr_Y^* ⋙ φ̄^*`
defining the Weil structure of `φ^* F` is monoidal. Hence a pairing of Weil sheaves compatible
with the Weil structures pulls back to a compatible pairing
(`AlgebraicGeometry.ProEtale.upperStarStr_pairing`). Applied to the evaluation, this
shows that the comparison `φ^* [A, B] ⟶ [φ^* A, φ^* B]`
(`AlgebraicGeometry.ProEtale.adicUpperStarIhomComparison`) is a morphism of pro-étale Weil
sheaves (`AlgebraicGeometry.ProEtaleWeilSheaf.upperStarIhomComparison_comm`). All computations
are done for an arbitrary exchange square `a ≫ j = j ≫ b`, so that the kernel never has to
unfold the geometric Frobenius. The comparison is an isomorphism for `A` lisse, which gives
`AlgebraicGeometry.ProEtaleWeilSheaf.ihomFunctorCompUpperStarIso`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Endofunctor

namespace CategoryTheory.NatTrans

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]

/-- A composite of monoidal natural isomorphisms is monoidal. -/
lemma isMonoidal_trans_hom {F G H : C ⥤ D} [F.LaxMonoidal] [G.LaxMonoidal]
    [H.LaxMonoidal] (e₁ : F ≅ G) (e₂ : G ≅ H) (h₁ : IsMonoidal e₁.hom)
    (h₂ : IsMonoidal e₂.hom) : IsMonoidal (e₁ ≪≫ e₂).hom := by
  rw [Iso.trans_hom]
  infer_instance

/-- The inverse of a monoidal natural isomorphism is monoidal. -/
lemma isMonoidal_symm_hom {F G : C ⥤ D} [F.LaxMonoidal] [G.LaxMonoidal]
    (e : F ≅ G) (h : IsMonoidal e.hom) : IsMonoidal e.symm.hom := by
  rw [Iso.symm_hom]
  infer_instance

/-- A whiskering of a monoidal natural isomorphism is monoidal. -/
lemma isMonoidal_isoWhiskerLeft_hom {E : Type*} [Category E] [MonoidalCategory E]
    (F : C ⥤ D) {G H : D ⥤ E} [F.LaxMonoidal] [G.LaxMonoidal] [H.LaxMonoidal]
    (e : G ≅ H) (h : IsMonoidal e.hom) : IsMonoidal (Functor.isoWhiskerLeft F e).hom := by
  rw [Functor.isoWhiskerLeft_hom]
  infer_instance

/-- A whiskering of a monoidal natural isomorphism is monoidal. -/
lemma isMonoidal_isoWhiskerRight_hom {E : Type*} [Category E] [MonoidalCategory E]
    {F G : C ⥤ D} (H : D ⥤ E) [F.LaxMonoidal] [G.LaxMonoidal] [H.LaxMonoidal]
    (e : F ≅ G) (h : IsMonoidal e.hom) : IsMonoidal (Functor.isoWhiskerRight e H).hom := by
  rw [Functor.isoWhiskerRight_hom]
  infer_instance

end CategoryTheory.NatTrans

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {X Y : Scheme.{u}} (j : X ⟶ Y) (a : X ≅ X) (b : Y ≅ Y)
  (c : a.hom ≫ j = j ≫ b.hom)

/-- The exchange isomorphism `j^* ⋙ (a⁻¹)_* ≅ (b⁻¹)_* ⋙ j^*` is monoidal. -/
instance isMonoidal_upperStarExchangeIso_hom :
    NatTrans.IsMonoidal (upperStarExchangeIso (WeilCoefficients.{u} l) j a b c).hom :=
  NatTrans.isMonoidal_trans_hom _ _
    (NatTrans.isMonoidal_isoWhiskerLeft_hom _ _ (NatTrans.isMonoidal_symm_hom _ inferInstance))
    (NatTrans.isMonoidal_trans_hom _ _ (NatTrans.isMonoidal_symm_hom _ inferInstance)
      (NatTrans.isMonoidal_trans_hom _ _ inferInstance
        (NatTrans.isMonoidal_trans_hom _ _ inferInstance
          (NatTrans.isMonoidal_isoWhiskerRight_hom _ _ inferInstance))))

/-- The components of the exchange isomorphism. -/
lemma upperStarExchangeIso_hom_app (M) :
    (upperStarExchangeIso (WeilCoefficients.{u} l) j a b c).hom.app M =
      (upperStarIsoLowerStarInv (WeilCoefficients.{u} l) a).inv.app
          ((j)^*[WeilCoefficients.{u} l].obj M) ≫
        (upperStarComp _ a.hom j).inv.app M ≫ (upperStarCongr _ c).hom.app M ≫
        (upperStarComp _ j b.hom).hom.app M ≫
        (j)^*[WeilCoefficients.{u} l].map
          ((upperStarIsoLowerStarInv (WeilCoefficients.{u} l) b).hom.app M) := by
  simp only [upperStarExchangeIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]

-- Stated for a variable isomorphism `α`: for `α = upperStarIsoLowerStarInv` the kernel times out
-- comparing the two objects.
private lemma inv_app_adicUpperStar_obj_X
    {P Q : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l) ⥤
      Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)} (α : P ≅ Q)
    (M : AdicSheaf l Y) :
    α.inv.app ((j)^*ᵃ[l].obj M).X = α.inv.app ((j)^*[WeilCoefficients.{u} l].obj M.X) :=
  rfl

variable (l) in
/-- The exchange isomorphism `j^* ⋙ (a⁻¹)_* ≅ (b⁻¹)_* ⋙ j^*` of `ℓ`-adic pullbacks along a
commutative square `a ≫ j = j ≫ b` with `a`, `b` isomorphisms. -/
noncomputable abbrev adicUpperStarExchangeIso :
    (j)^*ᵃ[l] ⋙ (a.inv)_*ᵃ[l] ≅ (b.inv)_*ᵃ[l] ⋙ (j)^*ᵃ[l] :=
  Functor.isoWhiskerLeft _ (adicUpperStarIsoLowerStarInv l a).symm ≪≫
    (adicUpperStarComp l _ _).symm ≪≫ adicUpperStarCongr l c ≪≫ adicUpperStarComp l _ _ ≪≫
    Functor.isoWhiskerRight (adicUpperStarIsoLowerStarInv l b) _

/-- The exchange isomorphism of `ℓ`-adic pullbacks is, on underlying sheaves, the exchange
isomorphism `AlgebraicGeometry.ProEtale.upperStarExchangeIso`. Stated for arbitrary `j`, `a`,
`b`: for the geometric Frobenii the kernel times out on the same proof. -/
lemma adicUpperStarExchangeIso_hom_app_hom (M : AdicSheaf l Y) :
    ((adicUpperStarExchangeIso l j a b c).hom.app M).hom =
      (upperStarExchangeIso (WeilCoefficients.{u} l) j a b c).hom.app M.X := by
  rw [upperStarExchangeIso_hom_app]
  simp only [Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Mod.comp_hom', adicUpperStar_map_hom,
    adicUpperStarIsoLowerStarInv_inv_app_hom, adicUpperStarIsoLowerStarInv_hom_app_hom,
    adicUpperStarComp_inv_app_hom, adicUpperStarComp_hom_app_hom, adicUpperStarCongr_hom_app_hom]
  rw [inv_app_adicUpperStar_obj_X]

variable {j a b c}

variable (l) in
/-- The structure isomorphism `(b⁻¹)_* 𝓗om(A, B) ≅ 𝓗om(A, B)` induced by isomorphisms
`(b⁻¹)_* A ≅ A` and `(b⁻¹)_* B ≅ B`; for the geometric Frobenius `b` this is the Weil
structure of `AlgebraicGeometry.ProEtaleWeilSheaf.ihom`. -/
noncomputable abbrev ihomStr {Z : Scheme.{u}} (b : Z ≅ Z) {A B : AdicSheaf l Z}
    (sA : (b.inv)_*ᵃ[l].obj A ≅ A) (sB : (b.inv)_*ᵃ[l].obj B ≅ B) :
    (b.inv)_*ᵃ[l].obj ((AdicSheaf.ihom A).obj B) ≅ (AdicSheaf.ihom A).obj B :=
  (adicLowerStarCompIhomIso l b.inv A).symm.app B ≪≫ (Mod.ihomMapIso sA.symm).app _ ≪≫
    (AdicSheaf.ihom A).mapIso sB

/-- The evaluation `𝓗om(A, B) ⊗ A ⟶ B` is compatible with the structure isomorphisms. -/
lemma ihomStr_evaluation {Z : Scheme.{u}} (b : Z ≅ Z) {A B : AdicSheaf l Z}
    (sA : (b.inv)_*ᵃ[l].obj A ≅ A) (sB : (b.inv)_*ᵃ[l].obj B ≅ B) :
    ((ihomStr l b sA sB).hom.hom ⊗ₘ sA.hom.hom) ≫ Mod.evaluation A B =
      μ (b.inv)_*[WeilCoefficients.{u} l] ((AdicSheaf.ihom A).obj B).X A.X ≫
        (b.inv)_*[WeilCoefficients.{u} l].map (Mod.evaluation A B) ≫ sB.hom.hom := by
  have : (Mod.mapModComap (G := (b.inv)_*[WeilCoefficients.{u} l])
      (adicConstantSheafToLowerStar l b.inv)).IsEquivalence := isEquivalence_adicLowerStar l _
  have h := Mod.μ_comp_map_evaluation (adicConstantSheafToLowerStar l b.inv)
    (fun _ _ ↦ Functor.LaxBraided.braided _ _) A B
  have hstr : (ihomStr l b sA sB).hom.hom =
      ((adicLowerStarCompIhomIso l b.inv A).inv.app B).hom ≫
      ((Mod.ihomMap sA.inv).app _).hom ≫ ((AdicSheaf.ihom A).map sB.hom).hom := rfl
  have hφ : sA.hom.hom ≫ sA.inv.hom = 𝟙 _ := by
    rw [← Mod.comp_hom', Iso.hom_inv_id, Mod.id_hom']
  rw [hstr, tensorHom_def', comp_whiskerRight, comp_whiskerRight]
  simp only [Category.assoc]
  rw [Mod.evaluation_naturality A sB.hom, Mod.evaluation_ihomMap_assoc sA.inv]
  erw [← whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, hφ,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]
  erw [reassoc_of% h]
  rfl

variable (l c) in
/-- The structure isomorphism `(a⁻¹)_* j^* M ≅ j^* M` induced by `(b⁻¹)_* M ≅ M` along the
exchange isomorphism; for the geometric Frobenii this is the Weil structure of
`AlgebraicGeometry.ProEtaleWeilSheaf.upperStar`. -/
noncomputable abbrev upperStarStr {M : AdicSheaf l Y} (sM : (b.inv)_*ᵃ[l].obj M ≅ M) :
    (a.inv)_*ᵃ[l].obj ((j)^*ᵃ[l].obj M) ≅ (j)^*ᵃ[l].obj M :=
  (adicUpperStarExchangeIso l j a b c).app M ≪≫ (j)^*ᵃ[l].mapIso sM

/-- The underlying morphism of the transported structure isomorphism. -/
lemma upperStarStr_hom_hom {M : AdicSheaf l Y} (sM : (b.inv)_*ᵃ[l].obj M ≅ M) :
    (upperStarStr l c sM).hom.hom =
      (upperStarExchangeIso (WeilCoefficients.{u} l) j a b c).hom.app M.X ≫
        (j)^*[WeilCoefficients.{u} l].map sM.hom.hom := by
  rw [Iso.trans_hom, Mod.comp_hom', Iso.app_hom, adicUpperStarExchangeIso_hom_app_hom,
    Functor.mapIso_hom, adicUpperStar_map_hom]

/-- **Pullbacks of compatible pairings are compatible.** -/
theorem upperStarStr_pairing {P Q R : AdicSheaf l Y} (sP : (b.inv)_*ᵃ[l].obj P ≅ P)
    (sQ : (b.inv)_*ᵃ[l].obj Q ≅ Q) (sR : (b.inv)_*ᵃ[l].obj R ≅ R)
    (e : P.X ⊗ Q.X ⟶ R.X)
    (h : (sP.hom.hom ⊗ₘ sQ.hom.hom) ≫ e =
      μ (b.inv)_*[WeilCoefficients.{u} l] P.X Q.X ≫ (b.inv)_*[_].map e ≫ sR.hom.hom) :
    ((upperStarStr l c sP).hom.hom ⊗ₘ (upperStarStr l c sQ).hom.hom) ≫
        (μ (j)^*[WeilCoefficients.{u} l] P.X Q.X ≫ (j)^*[_].map e) =
      μ (a.inv)_*[WeilCoefficients.{u} l] ((j)^*[_].obj P.X) ((j)^*[_].obj Q.X) ≫
        (a.inv)_*[_].map (μ (j)^*[WeilCoefficients.{u} l] P.X Q.X ≫ (j)^*[_].map e) ≫
          (upperStarStr l c sR).hom.hom := by
  have hψ := NatTrans.IsMonoidal.tensor
    (τ := (upperStarExchangeIso (WeilCoefficients.{u} l) j a b c).hom) P.X Q.X
  have nψ := (upperStarExchangeIso (WeilCoefficients.{u} l) j a b c).hom.naturality e
  simp only [Functor.LaxMonoidal.comp_μ, Functor.comp_map, Functor.comp_obj] at hψ nψ
  rw [upperStarStr_hom_hom, upperStarStr_hom_hom, upperStarStr_hom_hom,
    ← tensorHom_comp_tensorHom_assoc, μ_natural_assoc, ← Functor.map_comp, h]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hψ, reassoc_of% nψ]

/-- A morphism `κ : M ⟶ 𝓗om(D, N)` whose uncurried form `M ⊗ D ⟶ N` is compatible with
structure isomorphisms `(b⁻¹)_* M ≅ M`, `(b⁻¹)_* D ≅ D`, `(b⁻¹)_* N ≅ N` intertwines the
structure isomorphism of `M` with the one of the internal hom (`ihomStr`). For the geometric
Frobenius this is `AlgebraicGeometry.ProEtaleWeilSheaf.homToIhom_comm`. -/
theorem ihomStr_comm_of_pairing {Z : Scheme.{u}} (b : Z ≅ Z) {M D N : AdicSheaf l Z}
    (sM : (b.inv)_*ᵃ[l].obj M ≅ M) (sD : (b.inv)_*ᵃ[l].obj D ≅ D)
    (sN : (b.inv)_*ᵃ[l].obj N ≅ N) (κ : M ⟶ (AdicSheaf.ihom D).obj N)
    (hκ : (sM.hom.hom ⊗ₘ sD.hom.hom) ≫ (κ.hom ▷ D.X ≫ Mod.evaluation D N) =
      μ (b.inv)_*[WeilCoefficients.{u} l] M.X D.X ≫
        (b.inv)_*[_].map (κ.hom ▷ D.X ≫ Mod.evaluation D N) ≫ sN.hom.hom) :
    (b.inv)_*ᵃ[l].map κ ≫ (ihomStr l b sD sN).hom = sM.hom ≫ κ := by
  set Fr := (b.inv)_*[WeilCoefficients.{u} l]
  have : IsIso sD.hom.hom := inferInstanceAs (IsIso ((Mod.forget _).map sD.hom))
  have he := ihomStr_evaluation b sD sN
  apply Mod.hom_ext
  rw [Mod.comp_hom', Mod.comp_hom', adicLowerStar_map_hom]
  apply Mod.hom_ext_of_evaluation (D := D)
  rw [← cancel_epi (Fr.obj M.X ◁ sD.hom.hom), comp_whiskerRight_assoc,
    whisker_exchange_assoc, ← tensorHom_def'_assoc, he, comp_whiskerRight_assoc,
    ← tensorHom_def'_assoc]
  erw [hκ]
  rw [Fr.map_comp_assoc, ← reassoc_of% (μ_natural_left Fr κ.hom D.X)]
  rfl

variable (c)

/-- **The comparison `j^* 𝓗om(A, B) ⟶ 𝓗om(j^* A, j^* B)` is compatible with the structure
isomorphisms** transported along an exchange square `a ≫ j = j ≫ b`. -/
theorem upperStarStr_ihomComparison {A B : AdicSheaf l Y} (sA : (b.inv)_*ᵃ[l].obj A ≅ A)
    (sB : (b.inv)_*ᵃ[l].obj B ≅ B) :
    (a.inv)_*ᵃ[l].map (adicUpperStarIhomComparison l j A B) ≫
        (ihomStr l a (upperStarStr l c sA) (upperStarStr l c sB)).hom =
      (upperStarStr l c (ihomStr l b sA sB)).hom ≫ adicUpperStarIhomComparison l j A B := by
  apply ihomStr_comm_of_pairing
  have h3 := uncurryHom_adicUpperStarIhomComparison j A B
  rw [Mod.uncurryHom] at h3
  rw [h3]
  exact upperStarStr_pairing (c := c) (ihomStr l b sA sB) sA sB (Mod.evaluation A B)
    (ihomStr_evaluation b sA sB)

/-- `AlgebraicGeometry.ProEtale.upperStarStr_ihomComparison` with the structure isomorphisms
given as variables equal to the transported ones; this form applies to pro-étale Weil sheaves
without the kernel having to unfold their constructions. -/
theorem upperStarStr_ihomComparison_of_eq {A B : AdicSheaf l Y} (sA : (b.inv)_*ᵃ[l].obj A ≅ A)
    (sB : (b.inv)_*ᵃ[l].obj B ≅ B) (sM : (b.inv)_*ᵃ[l].obj ((AdicSheaf.ihom A).obj B) ≅
      (AdicSheaf.ihom A).obj B)
    (tA : (a.inv)_*ᵃ[l].obj ((j)^*ᵃ[l].obj A) ≅ (j)^*ᵃ[l].obj A)
    (tB : (a.inv)_*ᵃ[l].obj ((j)^*ᵃ[l].obj B) ≅ (j)^*ᵃ[l].obj B)
    (tH : (a.inv)_*ᵃ[l].obj ((AdicSheaf.ihom ((j)^*ᵃ[l].obj A)).obj ((j)^*ᵃ[l].obj B)) ≅
      (AdicSheaf.ihom ((j)^*ᵃ[l].obj A)).obj ((j)^*ᵃ[l].obj B))
    (tM : (a.inv)_*ᵃ[l].obj ((j)^*ᵃ[l].obj ((AdicSheaf.ihom A).obj B)) ≅
      (j)^*ᵃ[l].obj ((AdicSheaf.ihom A).obj B))
    (htA : tA = upperStarStr l c sA) (htB : tB = upperStarStr l c sB)
    (hsM : sM = ihomStr l b sA sB) (htH : tH = ihomStr l a tA tB)
    (htM : tM = upperStarStr l c sM) :
    (a.inv)_*ᵃ[l].map (adicUpperStarIhomComparison l j A B) ≫ tH.hom =
      tM.hom ≫ adicUpperStarIhomComparison l j A B := by
  subst htA htB hsM htH htM
  exact upperStarStr_ihomComparison c sA sB

variable {k : Type u} [Field k] [Finite k] {X₀ Y₀ : Scheme.{u}} {f : X₀ ⟶ Spec (.of k)}
  {g : Y₀ ⟶ Spec (.of k)} (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f)

/-- The exchange isomorphism of the Weil structure of a pullback is an instance of
`AlgebraicGeometry.ProEtale.adicUpperStarExchangeIso`. -/
lemma adicUpperStarGeometricFiberMapCompFrobeniusIso_eq :
    adicUpperStarGeometricFiberMapCompFrobeniusIso l φ h =
      adicUpperStarExchangeIso l (Scheme.Hom.geometricFiberMap φ h) f.geometricGaloisFrobenius.asIso
        g.geometricGaloisFrobenius.asIso
        (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ h).symm :=
  rfl

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
variable (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]

/-- The Weil structure of the internal hom, as the structure isomorphism `ihomStr`. -/
lemma ihom_str_hom (A B : ProEtaleWeilSheaf k₀ l X) :
    (ihom k₀ l X A B).str.hom =
      (ihomStr l (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso A.str B.str).hom :=
  rfl

/-- The Weil structure of the internal hom is `ihomStr`. -/
lemma ihom_str (A B : ProEtaleWeilSheaf k₀ l X) :
    (ihom k₀ l X A B).str =
      ihomStr l (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso A.str B.str :=
  IsoAlgebra.mk_str _ _

/-- The Weil structure of a pullback, as the structure isomorphism `upperStarStr`. -/
lemma upperStar_obj_str_hom (A : ProEtaleWeilSheaf k₀ l Y) :
    ((upperStar k₀ l φ).obj A).str.hom =
      (upperStarStr l (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ
        (comp_over φ (Spec (CommRingCat.of k₀)))).symm A.str).hom := by
  unfold ProEtaleWeilSheaf.upperStar
  rw [IsoAlgebra.mapOfNatIso_obj_str, adicUpperStarGeometricFiberMapCompFrobeniusIso_eq]

/-- The Weil structure of a pullback is `upperStarStr`. -/
lemma upperStar_obj_str (A : ProEtaleWeilSheaf k₀ l Y) :
    ((upperStar k₀ l φ).obj A).str =
      upperStarStr l (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ
        (comp_over φ (Spec (CommRingCat.of k₀)))).symm A.str :=
  Iso.ext (upperStar_obj_str_hom φ A)

/-- The internal hom functor on objects. -/
lemma ihomFunctor_obj (A B : ProEtaleWeilSheaf k₀ l X) :
    (ihomFunctor k₀ l X A).obj B = ihom k₀ l X A B :=
  rfl

/-- The comparison `φ^* [A, B] ⟶ [φ^* A, φ^* B]` is compatible with the Weil structures. -/
lemma upperStarIhomComparison_comm (A B : ProEtaleWeilSheaf k₀ l Y) :
    (WeilSheaf.frobeniusPullback k₀ l X).map (adicUpperStarIhomComparison l
        (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))
        A.carrier B.carrier) ≫
      ((ihomFunctor k₀ l X ((upperStar k₀ l φ).obj A)).obj ((upperStar k₀ l φ).obj B)).obj.str =
    ((upperStar k₀ l φ).obj ((ihomFunctor k₀ l Y A).obj B)).obj.str ≫
      adicUpperStarIhomComparison l
        (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))
        A.carrier B.carrier := by
  rw [← IsoAlgebra.str_hom, ← IsoAlgebra.str_hom]
  exact upperStarStr_ihomComparison_of_eq _ A.str B.str _ _ _ _ _ (upperStar_obj_str φ A)
    (upperStar_obj_str φ B) (ihom_str A B) (ihom_str _ _) (upperStar_obj_str φ _)

variable [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]

/-- **Pullback commutes with the internal hom out of a lisse pro-étale Weil sheaf**:
`φ^* [A, -] ≅ [φ^* A, φ^* -]`. -/
noncomputable def ihomFunctorCompUpperStarIso (A : ProEtaleWeilSheaf k₀ l Y)
    (hA : IsAdicLisseSheaf A.carrier) :
    ihomFunctor k₀ l Y A ⋙ upperStar k₀ l φ ≅
      upperStar k₀ l φ ⋙ ihomFunctor k₀ l X ((upperStar k₀ l φ).obj A) :=
  NatIso.ofComponents (fun B ↦
    have := hA.isIso_adicUpperStarIhomComparison
      (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀)))) B.carrier
    IsoAlgebra.isoMk (asIso (adicUpperStarIhomComparison l
      (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))
      A.carrier B.carrier)) (upperStarIhomComparison_comm φ A B))
    fun f ↦ IsoAlgebra.hom_ext (adicUpperStarIhomComparison_naturality _ _ f.hom.f)

end AlgebraicGeometry.ProEtaleWeilSheaf
