/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius.FiberMapCongr
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraTwist
public import WeilConjectures.WeilSheaf.TorsorPairing
public import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction

/-!
# Isotypic components of pushforwards along split torsors of Weil sheaves

Let `π : W ⟶ Z` be an étale morphism of `k₀`-schemes and `τ_g`, `g ∈ G`, automorphisms of `W`
over `Z` and over `k₀`, forming a torsor under the finite abelian group `G` which is split by
the `τ_g` (`AlgebraicGeometry.ProEtale.IsTorsorSplit`). The group acts on the pushforward
`P = π_* ℚ̄_ℓ` of the constant pro-étale Weil sheaf by morphisms of pro-étale Weil sheaves
(`AlgebraicGeometry.ProEtaleWeilSheaf.torsorTranslation`), and for a character `χ` of `G` the
endomorphism `e_χ = |G|⁻¹ ∑_g χ(-g) σ_g` (`AlgebraicGeometry.ProEtaleWeilSheaf.torsorIdempotent`)
projects onto the `χ`-isotypic component.

The main result (`AlgebraicGeometry.ProEtaleWeilSheaf.nonempty_iso_ihom_of_isotypic`) is the Weil
version of `AlgebraicGeometry.ProEtale.isIso_torsorPairingCurry`: given morphisms of pro-étale
Weil sheaves `φᵢ : Mᵢ ⟶ P` on which `G` acts through `χ₁`, `χ₂` and `χ₁ χ₂`, whose adjoints
`π^* Mᵢ ⟶ ℚ̄_ℓ` are isomorphisms, the product of functions induces an isomorphism of pro-étale
Weil sheaves `M₁ ≅ [M₂, M₃]`: the Weil structure of `P` is compatible with the product of
functions, being induced by morphisms of schemes over `k₀`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite Functor.LaxMonoidal
open scoped Obj

namespace AlgebraicGeometry

open scoped ProEtale

namespace Scheme.Hom

variable {k : Type u} [Field k] {X₀ Y₀ : Scheme.{u}} {f : X₀ ⟶ Spec (.of k)}
  {g : Y₀ ⟶ Spec (.of k)}

/-- The base change `e × 𝟙 : X₀ ×_{Spec k} Spec k̄ ≅ Y₀ ×_{Spec k} Spec k̄` of an isomorphism
`e : X₀ ≅ Y₀` of schemes over `k`. -/
noncomputable def geometricFiberMapIso (e : X₀ ≅ Y₀) (h : e.hom ≫ g = f) :
    f.geometricFiber ≅ g.geometricFiber where
  hom := geometricFiberMap e.hom h
  inv := geometricFiberMap e.inv (by rw [← h, Iso.inv_hom_id_assoc])
  hom_inv_id := by
    rw [← geometricFiberMap_comp]
    simp only [Iso.hom_inv_id]
    exact geometricFiberMap_id
  inv_hom_id := by
    rw [← geometricFiberMap_comp]
    simp only [Iso.inv_hom_id]
    exact geometricFiberMap_id

/-- The underlying morphism of `AlgebraicGeometry.Scheme.Hom.geometricFiberMapIso`
(blueprint `lemma-artin-schreier-character-sheaf`). -/
@[simp]
lemma geometricFiberMapIso_hom (e : X₀ ≅ Y₀) (h : e.hom ≫ g = f) :
    (geometricFiberMapIso e h).hom = geometricFiberMap e.hom h :=
  rfl

end Scheme.Hom


section Weil

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]

section Scalar

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- Multiplication by a scalar `b ∈ ℚ̄_ℓ`, as an endomorphism of a pro-étale Weil sheaf: the
Frobenius pullback, a pushforward, commutes with it. -/
noncomputable def ProEtaleWeilSheaf.smulEnd (b : PadicAlgCl l) (A : ProEtaleWeilSheaf k₀ l X) :
    A ⟶ A :=
  ObjectProperty.homMk ⟨ProEtale.AdicSheaf.smul (ULift.up b) A.carrier, by
    rw [ProEtale.AdicSheaf.adicLowerStar_map_smul, ProEtale.AdicSheaf.smul_comp]⟩

/-- The underlying morphism of `AlgebraicGeometry.ProEtaleWeilSheaf.smulEnd`
(blueprint `lemma-artin-schreier-character-sheaf`). -/
@[simp]
lemma ProEtaleWeilSheaf.smulEnd_hom_f (b : PadicAlgCl l) (A : ProEtaleWeilSheaf k₀ l X) :
    (ProEtaleWeilSheaf.smulEnd b A).hom.f = ProEtale.AdicSheaf.smul (ULift.up b) A.carrier :=
  rfl

/-- Scalar multiplication commutes with morphisms (blueprint
`lemma-artin-schreier-character-sheaf`). -/
lemma ProEtaleWeilSheaf.smulEnd_comp (b : PadicAlgCl l) {A B : ProEtaleWeilSheaf k₀ l X}
    (f : A ⟶ B) : ProEtaleWeilSheaf.smulEnd b A ≫ f = f ≫ ProEtaleWeilSheaf.smulEnd b B :=
  ObjectProperty.hom_ext _ (Endofunctor.Algebra.Hom.ext (ProEtale.AdicSheaf.smul_comp _ _))

/-- Scalar multiplication is multiplicative in the scalar
(blueprint `lemma-artin-schreier-character-sheaf`). -/
lemma ProEtaleWeilSheaf.smulEnd_smulEnd (b c : PadicAlgCl l) (A : ProEtaleWeilSheaf k₀ l X) :
    ProEtaleWeilSheaf.smulEnd b A ≫ ProEtaleWeilSheaf.smulEnd c A =
      ProEtaleWeilSheaf.smulEnd (c * b) A :=
  ObjectProperty.hom_ext _ (Endofunctor.Algebra.Hom.ext (ProEtale.AdicSheaf.smul_smul _ _ _))

/-- Scalar multiplication by `1` is the identity (blueprint
`lemma-artin-schreier-character-sheaf`). -/
lemma ProEtaleWeilSheaf.smulEnd_one (A : ProEtaleWeilSheaf k₀ l X) :
    ProEtaleWeilSheaf.smulEnd 1 A = 𝟙 A :=
  ObjectProperty.hom_ext _ (Endofunctor.Algebra.Hom.ext (ProEtale.AdicSheaf.smul_one _))

/-- Scalar multiplication is additive in the scalar (blueprint
`lemma-artin-schreier-character-sheaf`). -/
lemma ProEtaleWeilSheaf.smulEnd_add (b c : PadicAlgCl l) (A : ProEtaleWeilSheaf k₀ l X) :
    ProEtaleWeilSheaf.smulEnd (b + c) A =
      ProEtaleWeilSheaf.smulEnd b A + ProEtaleWeilSheaf.smulEnd c A :=
  ObjectProperty.hom_ext _ (Endofunctor.Algebra.Hom.ext (Mod.hom_ext _ _ (by
    change (ULift.up (b + c) : ULift.{u + 1} (PadicAlgCl l)) • 𝟙 _ =
      (ULift.up b : ULift.{u + 1} (PadicAlgCl l)) • 𝟙 _ +
        (ULift.up c : ULift.{u + 1} (PadicAlgCl l)) • 𝟙 _
    rw [← add_smul]
    rfl)))

/-- A sum of scalar multiplications is the scalar multiplication by the sum
(blueprint `lemma-artin-schreier-character-sheaf`). -/
lemma ProEtaleWeilSheaf.sum_smulEnd {ι : Type*} (s : Finset ι) (b : ι → PadicAlgCl l)
    (A : ProEtaleWeilSheaf k₀ l X) :
    ∑ i ∈ s, ProEtaleWeilSheaf.smulEnd (b i) A = ProEtaleWeilSheaf.smulEnd (∑ i ∈ s, b i) A := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact ObjectProperty.hom_ext _ (Endofunctor.Algebra.Hom.ext (Mod.hom_ext _ _ (by
      change 0 = (ULift.up 0 : ULift.{u + 1} (PadicAlgCl l)) • 𝟙 _
      rw [show (ULift.up 0 : ULift.{u + 1} (PadicAlgCl l)) = 0 from rfl, zero_smul])))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, ProEtaleWeilSheaf.smulEnd_add]

end Scalar

section Torsor

/-- The Weil structure of the constant pro-étale Weil sheaf
(blueprint `lemma-artin-schreier-character-sheaf`). -/
lemma ProEtaleWeilSheaf.adicConstant_str_hom_hom (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))] :
    (ProEtaleWeilSheaf.adicConstant k₀ l X).str.hom.hom =
      (ProEtale.adicConstantSheafLowerStarIso l
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.symm).hom :=
  rfl

variable {Z W : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [W.Over (Spec (CommRingCat.of k₀))] (π : W ⟶ Z) [π.IsOver (Spec (CommRingCat.of k₀))]
  {G : Type u} (τ : G → (W ≅ W)) [hτk : ∀ g, (τ g).hom.IsOver (Spec (CommRingCat.of k₀))]
  (hτ : ∀ g, (τ g).hom ≫ π = π)

variable (k₀) in
/-- The base change `τ̄_g` of the automorphism `τ_g` to the geometric fibre. -/
noncomputable abbrev geometricTorsorAut (g : G) :
    (W ↘ Spec (CommRingCat.of k₀)).geometricFiber ≅ (W ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
  Scheme.Hom.geometricFiberMapIso (τ g) (comp_over (τ g).hom _)

local notation "π̄" => Scheme.Hom.geometricFiberMap π (comp_over π (Spec (CommRingCat.of k₀)))

omit [Finite k₀] in
variable (k₀) in
/-- The base changes of the automorphisms of a torsor lie over the base
(blueprint `lemma-artin-schreier-character-sheaf`). -/
lemma geometricTorsorAut_comp (hτ : ∀ g, (τ g).hom ≫ π = π) (g : G) :
    (geometricTorsorAut k₀ τ g).hom ≫ π̄ = π̄ := by
  rw [Scheme.Hom.geometricFiberMapIso_hom, ← Scheme.Hom.geometricFiberMap_comp]
  exact Scheme.Hom.geometricFiberMap_congr (hτ g) _ _

variable (k₀ l) in
/-- The pushforward `π_* ℚ̄_ℓ` of the constant pro-étale Weil sheaf. -/
noncomputable abbrev ProEtaleWeilSheaf.torsorPushforward : ProEtaleWeilSheaf k₀ l Z :=
  (ProEtaleWeilSheaf.lowerStar k₀ l π).obj (ProEtaleWeilSheaf.adicConstant k₀ l W)

/-- The Weil structure of the pushforward of a pro-étale Weil sheaf: the exchange of `π̄_*` with
the Frobenius pushforwards followed by `π̄_*` of the Weil structure. -/
lemma ProEtaleWeilSheaf.lowerStar_obj_str (F : ProEtaleWeilSheaf k₀ l W) :
    ((ProEtaleWeilSheaf.lowerStar k₀ l π).obj F).str =
      (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l π (comp_over π _)).app
          F.carrier ≪≫ (π̄)_*ᵃ[l].mapIso F.str :=
  Endofunctor.IsoAlgebra.mapOfNatIso_obj_str _ F

/-- The Weil structure of `π_* ℚ̄_ℓ`, on underlying sheaves: the exchange of `π̄_*` with the
Frobenius pushforwards followed by `π̄_*` of the Weil structure of `ℚ̄_ℓ`. -/
lemma ProEtaleWeilSheaf.torsorPushforward_str_hom_hom' :
    (ProEtaleWeilSheaf.torsorPushforward k₀ l π).str.hom.hom =
      ((ProEtale.lowerStarComp _ π̄
          (Z ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv ≪≫
          ProEtale.lowerStarCongr _
            (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv _ _) ≪≫
          (ProEtale.lowerStarComp _
            (W ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv π̄).symm).app
          (ProEtaleWeilSheaf.adicConstant k₀ l W).carrier.X ≪≫
        (π̄)_*[WeilCoefficients.{u} l].mapIso
          (ProEtale.adicConstantSheafLowerStarIso l
            (W ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.symm)).hom := by
  rw [ProEtaleWeilSheaf.lowerStar_obj_str, Iso.trans_hom, Mod.comp_hom',
    Functor.mapIso_hom, ProEtale.adicLowerStar_map_hom]
  erw [ProEtaleWeilSheaf.adicConstant_str_hom_hom]
  rw [ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso, Iso.app_hom, Iso.trans_hom,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, NatTrans.comp_app, Mod.comp_hom',
    Mod.comp_hom', ProEtale.adicLowerStarComp_hom_app_hom, ProEtale.adicLowerStarComp_inv_app_hom,
    ProEtale.adicLowerStarCongr_hom_app_hom]
  simp only [Iso.trans_hom, Iso.app_hom, NatTrans.comp_app, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc]

/-- The Weil structure of `π_* ℚ̄_ℓ`, on underlying sheaves. -/
lemma ProEtaleWeilSheaf.torsorPushforward_str_hom_hom :
    (ProEtaleWeilSheaf.torsorPushforward k₀ l π).str.hom.hom =
      ((ProEtale.lowerStarComp _ π̄
          (Z ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv ≪≫
          ProEtale.lowerStarCongr _
            (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv _ _) ≪≫
          (ProEtale.lowerStarComp _
            (W ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv π̄).symm).app
          (ProEtale.adicConstantSheaf l (W ↘ Spec (CommRingCat.of k₀)).geometricFiber) ≪≫
        (π̄)_*[WeilCoefficients.{u} l].mapIso
          (ProEtale.adicConstantSheafLowerStarIso l
            (W ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.symm)).hom :=
  ProEtaleWeilSheaf.torsorPushforward_str_hom_hom' π

/-- The action of `τ_g` on `π_* ℚ̄_ℓ` commutes with its Weil structure: `τ_g` and `π` are
defined over `k₀`, hence commute with the geometric Frobenius. -/
lemma ProEtaleWeilSheaf.torsorTranslation_comm (g : G) :
    (WeilSheaf.frobeniusPullback k₀ l Z).map (ProEtale.torsorTranslation l π̄
        (geometricTorsorAut k₀ τ) (geometricTorsorAut_comp k₀ π τ hτ) g) ≫
        (ProEtaleWeilSheaf.torsorPushforward k₀ l π).obj.str =
      (ProEtaleWeilSheaf.torsorPushforward k₀ l π).obj.str ≫
        ProEtale.torsorTranslation l π̄ (geometricTorsorAut k₀ τ)
          (geometricTorsorAut_comp k₀ π τ hτ) g := by
  refine Mod.hom_ext _ _ ?_
  rw [Mod.comp_hom', Mod.comp_hom', ProEtale.adicLowerStar_map_hom,
    ProEtale.torsorTranslation_hom, ← Endofunctor.IsoAlgebra.str_hom,
    ProEtaleWeilSheaf.torsorPushforward_str_hom_hom]
  exact ProEtale.lowerStar_map_deckAction_comp_lowerStarExchange l π̄
    (W ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso
    (Z ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso
    (geometricTorsorAut k₀ τ g)
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv _ _)
    (geometricTorsorAut_comp k₀ π τ hτ g)
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius _ (comp_over (τ g).hom _)) _ rfl

/-- The action of `τ_g` on `π_* ℚ̄_ℓ`, pulling back sections along `τ_g`, as an endomorphism of
pro-étale Weil sheaves. -/
noncomputable def ProEtaleWeilSheaf.torsorTranslation (g : G) :
    ProEtaleWeilSheaf.torsorPushforward k₀ l π ⟶ ProEtaleWeilSheaf.torsorPushforward k₀ l π :=
  ObjectProperty.homMk ⟨ProEtale.torsorTranslation l π̄ (geometricTorsorAut k₀ τ)
    (geometricTorsorAut_comp k₀ π τ hτ) g, ProEtaleWeilSheaf.torsorTranslation_comm π τ hτ g⟩

/-- The underlying morphism of the translation of pro-étale Weil sheaves
(blueprint `lemma-artin-schreier-character-sheaf`). -/
@[simp]
lemma ProEtaleWeilSheaf.torsorTranslation_hom_f (g : G) :
    (ProEtaleWeilSheaf.torsorTranslation (l := l) π τ hτ g).hom.f =
      ProEtale.torsorTranslation l π̄ (geometricTorsorAut k₀ τ)
        (geometricTorsorAut_comp k₀ π τ hτ) g :=
  rfl

variable [AddCommGroup G] [Finite G]

/-- The projector `e_χ = |G|⁻¹ ∑_g χ(-g) σ_g` of `π_* ℚ̄_ℓ` onto its `χ`-isotypic component. -/
noncomputable def ProEtaleWeilSheaf.torsorIdempotent (χ : AddChar G (PadicAlgCl l)) :
    ProEtaleWeilSheaf.torsorPushforward k₀ l π ⟶ ProEtaleWeilSheaf.torsorPushforward k₀ l π :=
  letI := Fintype.ofFinite G
  ∑ g : G, ProEtaleWeilSheaf.smulEnd ((Nat.card G : PadicAlgCl l)⁻¹ * χ (-g)) _ ≫
    ProEtaleWeilSheaf.torsorTranslation π τ hτ g

/-- A morphism on which `G` acts through `χ` is fixed by the projector `e_χ`. -/
lemma ProEtaleWeilSheaf.comp_torsorIdempotent (χ : AddChar G (PadicAlgCl l))
    (hG : (Nat.card G : PadicAlgCl l) ≠ 0) {M : ProEtaleWeilSheaf k₀ l Z}
    (φ : M ⟶ ProEtaleWeilSheaf.torsorPushforward k₀ l π)
    (hφ : ∀ g, φ ≫ ProEtaleWeilSheaf.torsorTranslation π τ hτ g =
      ProEtaleWeilSheaf.smulEnd (χ g) M ≫ φ) :
    φ ≫ ProEtaleWeilSheaf.torsorIdempotent π τ hτ χ = φ := by
  let := Fintype.ofFinite G
  rw [ProEtaleWeilSheaf.torsorIdempotent, Preadditive.comp_sum]
  have (g : G) : φ ≫ ProEtaleWeilSheaf.smulEnd ((Nat.card G : PadicAlgCl l)⁻¹ * χ (-g)) _ ≫
      ProEtaleWeilSheaf.torsorTranslation π τ hτ g =
      ProEtaleWeilSheaf.smulEnd ((Nat.card G : PadicAlgCl l)⁻¹) M ≫ φ := by
    rw [← Category.assoc, ← ProEtaleWeilSheaf.smulEnd_comp, Category.assoc, hφ,
      ← Category.assoc, ProEtaleWeilSheaf.smulEnd_smulEnd, mul_left_comm,
      ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, mul_one]
  simp_rw [this]
  rw [← Preadditive.sum_comp, ProEtaleWeilSheaf.sum_smulEnd, Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, nsmul_eq_mul, mul_inv_cancel₀ hG,
    ProEtaleWeilSheaf.smulEnd_one, Category.id_comp]

/-- The Weil structure of `π_* ℚ̄_ℓ` is compatible with the product of functions. -/
@[reassoc]
lemma ProEtaleWeilSheaf.torsorPushforward_str_mul :
    ((ProEtaleWeilSheaf.torsorPushforward k₀ l π).str.hom.hom ⊗ₘ
        (ProEtaleWeilSheaf.torsorPushforward k₀ l π).str.hom.hom) ≫
      MonObj.mul (X := (π̄)_*[WeilCoefficients.{u} l].obj (ProEtale.adicConstantSheaf l
        (W ↘ Spec (CommRingCat.of k₀)).geometricFiber)) =
      μ ((Z ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[WeilCoefficients.{u}
          l]
          _ _ ≫
        ((Z ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[WeilCoefficients.{u}
          l].map
          (MonObj.mul (X := (π̄)_*[WeilCoefficients.{u} l].obj (ProEtale.adicConstantSheaf l
            (W ↘ Spec (CommRingCat.of k₀)).geometricFiber))) ≫
        (ProEtaleWeilSheaf.torsorPushforward k₀ l π).str.hom.hom := by
  rw [ProEtaleWeilSheaf.torsorPushforward_str_hom_hom]
  exact ProEtale.lowerStarExchange_mul π̄
    (Z ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.symm
    (W ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.symm
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv _ _)



/-- The underlying morphism of the projector `e_χ` of pro-étale Weil sheaves is the projector of
the underlying sheaves. -/
lemma ProEtaleWeilSheaf.torsorIdempotent_hom_f (χ : AddChar G (PadicAlgCl l)) :
    (ProEtaleWeilSheaf.torsorIdempotent π τ hτ χ).hom.f =
      ProEtale.torsorIdempotent l π̄ (geometricTorsorAut k₀ τ) (geometricTorsorAut_comp k₀ π τ hτ)
        χ := by
  let := Fintype.ofFinite G
  rw [ProEtaleWeilSheaf.torsorIdempotent, ProEtale.torsorIdempotent]
  change (Endofunctor.IsoAlgebra.forget _).map _ = _
  rw [Functor.map_sum]
  rfl

/-- **Pairings of isotypic components of pro-étale Weil sheaves.** -/
theorem ProEtaleWeilSheaf.nonempty_iso_ihom_of_isotypic [Etale π] [QuasiCompact π]
    [Surjective π] (hadd : ∀ g h, (τ (g + h)).hom = (τ g).hom ≫ (τ h).hom)
    (hsplit : ProEtale.IsTorsorSplit π τ hτ) (χ₁ χ₂ : AddChar G (PadicAlgCl l))
    (hG : (Nat.card G : PadicAlgCl l) ≠ 0) {M₁ M₂ M₃ : ProEtaleWeilSheaf k₀ l Z}
    (φ₁ : M₁ ⟶ ProEtaleWeilSheaf.torsorPushforward k₀ l π)
    (φ₂ : M₂ ⟶ ProEtaleWeilSheaf.torsorPushforward k₀ l π)
    (φ₃ : M₃ ⟶ ProEtaleWeilSheaf.torsorPushforward k₀ l π)
    (hφ₁ : ∀ g, φ₁ ≫ ProEtaleWeilSheaf.torsorTranslation π τ hτ g =
      ProEtaleWeilSheaf.smulEnd (χ₁ g) M₁ ≫ φ₁)
    (hφ₂ : ∀ g, φ₂ ≫ ProEtaleWeilSheaf.torsorTranslation π τ hτ g =
      ProEtaleWeilSheaf.smulEnd (χ₂ g) M₂ ≫ φ₂)
    (hφ₃ : ∀ g, φ₃ ≫ ProEtaleWeilSheaf.torsorTranslation π τ hτ g =
      ProEtaleWeilSheaf.smulEnd ((χ₁ * χ₂) g) M₃ ≫ φ₃)
    (hθ₁ : IsIso ((π̄)^*ᵃ[l].map φ₁.hom.f ≫
      (ProEtale.adicUpperStarLowerStarAdjunction l π̄).counit.app _))
    (hθ₂ : IsIso ((π̄)^*ᵃ[l].map φ₂.hom.f ≫
      (ProEtale.adicUpperStarLowerStarAdjunction l π̄).counit.app _))
    (hθ₃ : IsIso ((π̄)^*ᵃ[l].map φ₃.hom.f ≫
      (ProEtale.adicUpperStarLowerStarAdjunction l π̄).counit.app _)) :
    Nonempty (M₁ ≅ ProEtaleWeilSheaf.ihom k₀ l Z M₂ M₃) := by
  have : Etale π̄ := Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @Etale) _ _
    ‹_›
  have : Surjective π̄ :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @Surjective) _ _ ‹_›
  have : QuasiCompact π̄ :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @QuasiCompact) _ _ ‹_›
  have hτb := geometricTorsorAut_comp k₀ π τ hτ
  have hsplit' : ProEtale.IsTorsorSplit π̄ (geometricTorsorAut k₀ τ) hτb :=
    hsplit.of_isPullback (Scheme.Hom.isPullback_geometricFiberMap π _).flip _ hτb
      fun g ↦ Scheme.Hom.geometricFiberMap_comp_geometricFiberProj _ (comp_over (τ g).hom _)
  have hadd' (g h : G) : (geometricTorsorAut k₀ τ (g + h)).hom =
      (geometricTorsorAut k₀ τ g).hom ≫ (geometricTorsorAut k₀ τ h).hom := by
    simp only [Scheme.Hom.geometricFiberMapIso_hom]
    rw [← Scheme.Hom.geometricFiberMap_comp]
    exact Scheme.Hom.geometricFiberMap_congr (hadd g h) _ _
  have hgeom {M : ProEtaleWeilSheaf k₀ l Z} (φ : M ⟶ ProEtaleWeilSheaf.torsorPushforward k₀ l π)
      (χ : AddChar G (PadicAlgCl l))
      (hφ : ∀ g, φ ≫ ProEtaleWeilSheaf.torsorTranslation π τ hτ g =
        ProEtaleWeilSheaf.smulEnd (χ g) M ≫ φ) (g : G) :
      φ.hom.f ≫ ProEtale.torsorTranslation l π̄ (geometricTorsorAut k₀ τ) hτb g =
        ProEtale.AdicSheaf.smul (ULift.up (χ g)) M.carrier ≫ φ.hom.f :=
    congrArg (fun f ↦ f.hom.f) (hφ g)
  obtain ⟨r, hr₁, hr₂⟩ := ProEtale.exists_retraction_of_isotypic π̄ (geometricTorsorAut k₀ τ) hτb
    hadd' hsplit' (χ₁ * χ₂) hG φ₃.hom.f (hgeom φ₃ _ hφ₃) hθ₃
  set Fr :=
    ((Z ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[WeilCoefficients.{u} l]
  have hstr {A B : ProEtaleWeilSheaf k₀ l Z} (f : A ⟶ B) :
      Fr.map f.hom.f.hom ≫ B.str.hom.hom = A.str.hom.hom ≫ f.hom.f.hom := by
    have := congrArg Mod.Hom.hom f.hom.h
    rwa [Mod.comp_hom', Mod.comp_hom', ProEtale.adicLowerStar_map_hom] at this
  have hr : Fr.map r.hom ≫ M₃.str.hom.hom =
      (ProEtaleWeilSheaf.torsorPushforward k₀ l π).str.hom.hom ≫ r.hom := by
    have : Mono φ₃.hom.f.hom := by
      have h := congrArg Mod.Hom.hom hr₁
      rw [Mod.comp_hom', Mod.id_hom'] at h
      exact (IsSplitMono.mk' ⟨_, h⟩).mono
    rw [← cancel_mono φ₃.hom.f.hom, Category.assoc, ← hstr, ← Fr.map_comp_assoc, ← Mod.comp_hom',
      hr₂, Category.assoc, ← Mod.comp_hom', hr₂,
      ← ProEtaleWeilSheaf.torsorIdempotent_hom_f π τ hτ, hstr]
  have hp : (M₁.str.hom.hom ⊗ₘ M₂.str.hom.hom) ≫
      ProEtale.torsorPairing l π̄ φ₁.hom.f φ₂.hom.f r =
      μ Fr M₁.carrier.X M₂.carrier.X ≫ Fr.map (ProEtale.torsorPairing l π̄ φ₁.hom.f φ₂.hom.f r) ≫
        M₃.str.hom.hom := by
    rw [ProEtale.torsorPairing, tensorHom_comp_tensorHom_assoc, ← hstr φ₁, ← hstr φ₂,
      ← tensorHom_comp_tensorHom_assoc, ProEtaleWeilSheaf.torsorPushforward_str_mul_assoc, ← hr]
    erw [Functor.LaxMonoidal.μ_natural_assoc]
    rw [Fr.map_comp, Fr.map_comp, Category.assoc, Category.assoc]
  have hκ := hp
  rw [← ProEtale.AdicSheaf.curryHom_evaluation (ProEtale.torsorPairing l π̄ φ₁.hom.f φ₂.hom.f r)
    (ProEtale.isLinearRight_torsorPairing π̄ φ₁.hom.f φ₂.hom.f r)
    (ProEtale.torsorPairing_linear_left π̄ φ₁.hom.f φ₂.hom.f r)] at hκ
  have := ProEtale.isIso_torsorPairingCurry π̄ (geometricTorsorAut k₀ τ) hτb χ₁ χ₂ hG φ₁.hom.f
    φ₂.hom.f φ₃.hom.f r (hgeom φ₁ _ hφ₁) (hgeom φ₂ _ hφ₂) hr₂ hθ₁ hθ₂ hθ₃
  exact ⟨Endofunctor.IsoAlgebra.isoMk (asIso (ProEtale.torsorPairingCurry l π̄ φ₁.hom.f φ₂.hom.f r))
    (ProEtaleWeilSheaf.homToIhom_comm M₁ M₂ M₃ _ hκ)⟩

end Torsor

end Weil

end AlgebraicGeometry
