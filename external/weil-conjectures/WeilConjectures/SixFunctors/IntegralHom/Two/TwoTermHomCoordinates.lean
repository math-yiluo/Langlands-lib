/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Two.TwoTermTensorCoordinates
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Binary coordinates in the product Hom complex
Source: Stacks 0A8X and blueprint `lem-coef-integral-hom-reduction.proof.md`, paragraph 1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory.Limits

/-- Products commute with binary biproducts, expressed using arbitrary product fans.
Source: the product universal property, Stacks 0A8X.
(blueprint: lem-sf-two-term-hom-coordinates). -/
def productBinaryCoordinates
    {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
    {ι : Type w} {A B N : ι → C} (cA : Fan A) (cB : Fan B) (cN : Fan N)
    (hA : IsLimit cA) (hB : IsLimit cB) (hN : IsLimit cN)
    (e : ∀ i, N i ≅ A i ⊞ B i) : cN.pt ≅ cA.pt ⊞ cB.pt := by
  let l := hA.lift (Fan.mk cN.pt (fun i ↦ cN.proj i ≫ (e i).hom ≫ biprod.fst))
  let r := hB.lift (Fan.mk cN.pt (fun i ↦ cN.proj i ≫ (e i).hom ≫ biprod.snd))
  let f := biprod.lift l r
  let g := hN.lift (Fan.mk (cA.pt ⊞ cB.pt)
    (fun i ↦ biprod.map (cA.proj i) (cB.proj i) ≫ (e i).inv))
  have hl (i : ι) : l ≫ cA.proj i = cN.proj i ≫ (e i).hom ≫ biprod.fst :=
    hA.fac _ ⟨i⟩
  have hr (i : ι) : r ≫ cB.proj i = cN.proj i ≫ (e i).hom ≫ biprod.snd :=
    hB.fac _ ⟨i⟩
  have hg (i : ι) : g ≫ cN.proj i =
      biprod.map (cA.proj i) (cB.proj i) ≫ (e i).inv := hN.fac _ ⟨i⟩
  refine ⟨f, g, ?_, ?_⟩
  · apply hN.hom_ext
    intro ⟨i⟩
    change (f ≫ g) ≫ cN.proj i = 𝟙 _ ≫ cN.proj i
    rw [Category.assoc, hg]
    have hf : f ≫ biprod.map (cA.proj i) (cB.proj i) = cN.proj i ≫ (e i).hom := by
      apply biprod.hom_ext
      · simp only [Category.assoc, biprod.map_fst, biprod.lift_fst_assoc, f, hl]
      · simp only [Category.assoc, biprod.map_snd, biprod.lift_snd_assoc, f, hr]
    rw [← Category.assoc, hf]
    simp
  · apply biprod.hom_ext
    · apply hA.hom_ext
      intro ⟨i⟩
      change ((g ≫ f) ≫ biprod.fst) ≫ cA.proj i =
        (𝟙 _ ≫ biprod.fst) ≫ cA.proj i
      simp only [Category.assoc, f, biprod.lift_fst_assoc, hl]
      rw [← Category.assoc g (cN.proj i), hg]
      simp
    · apply hB.hom_ext
      intro ⟨i⟩
      change ((g ≫ f) ≫ biprod.snd) ≫ cB.proj i =
        (𝟙 _ ≫ biprod.snd) ≫ cB.proj i
      simp only [Category.assoc, f, biprod.lift_snd_assoc, hr]
      rw [← Category.assoc g (cN.proj i), hg]
      simp
@[reassoc]
theorem productBinaryCoordinates_hom_fst_proj
    {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
    {ι : Type w} {A B N : ι → C} (cA : Fan A) (cB : Fan B) (cN : Fan N)
    (hA : IsLimit cA) (hB : IsLimit cB) (hN : IsLimit cN)
    (e : ∀ i, N i ≅ A i ⊞ B i) (i : ι) :
    (productBinaryCoordinates cA cB cN hA hB hN e).hom ≫ biprod.fst ≫ cA.proj i =
      cN.proj i ≫ (e i).hom ≫ biprod.fst := by
  change biprod.lift _ _ ≫ biprod.fst ≫ cA.proj i = _
  rw [biprod.lift_fst_assoc]
  exact hA.fac _ ⟨i⟩
@[reassoc]
theorem productBinaryCoordinates_hom_snd_proj
    {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
    {ι : Type w} {A B N : ι → C} (cA : Fan A) (cB : Fan B) (cN : Fan N)
    (hA : IsLimit cA) (hB : IsLimit cB) (hN : IsLimit cN)
    (e : ∀ i, N i ≅ A i ⊞ B i) (i : ι) :
    (productBinaryCoordinates cA cB cN hA hB hN e).hom ≫ biprod.snd ≫ cB.proj i =
      cN.proj i ≫ (e i).hom ≫ biprod.snd := by
  change biprod.lift _ _ ≫ biprod.snd ≫ cB.proj i = _
  rw [biprod.lift_snd_assoc]
  exact hB.fac _ ⟨i⟩

end CategoryTheory.Limits

namespace WeilConjectures.IntegralHom

variable (Y : AlgebraicGeometry.Scheme.{t})
  (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})

attribute [local instance 2000] abSheafify abLocallyBijective

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

attribute [local irreducible] homComplexFunctor SheafOfModules.monoidalCategory totalTensor

local instance twoTermHomCoordinatesLocal1 :
    MonoidalCategory (Modules.{t, u} Y R) :=
  SheafOfModules.monoidalCategory R

local instance twoTermHomCoordinatesLocal2 : HasBinaryBiproducts (Modules.{t, u} Y R) :=
  HasBinaryBiproducts.of_hasBinaryProducts

/-- Additivity in the target of internal Hom, from sectionwise composition.
Source: Stacks 03EO (blueprint: lem-sf-two-term-hom-coordinates). -/
theorem twoTermHomAdditive (M : Modules.{t, u} Y R) :
    ((SheafOfModules.homFunctor R).obj (op M)).Additive where
  map_add := by
    intro X Z f g
    apply SheafOfModules.hom_ext
    ext U s
    rfl

attribute [local instance] twoTermHomAdditive

local instance twoTermHomCoordinatesLocal3 (M : Modules.{t, u} Y R) :
    PreservesBinaryBiproducts ((SheafOfModules.homFunctor R).obj (op M)) :=
  preservesBinaryBiproducts_of_preservesBinaryProducts _

/-- The involution multiplying a module by the parity sign.
Source: Stacks 0A8X, signs in the Hom complex.
(blueprint: lem-sf-two-term-hom-coordinates). -/
def parityIso (M : Modules.{t, u} Y R) (p : ℤ) : M ≅ M where
  hom := p.negOnePow • 𝟙 M
  inv := p.negOnePow • 𝟙 M
  hom_inv_id := by simp [Linear.comp_units_smul, smul_smul]
  inv_hom_id := by simp [Linear.comp_units_smul, smul_smul]

/-- The component coordinate isomorphism, with its parity correction.
Source: the finite-free calculation, Stacks 0A8X.
(blueprint: lem-sf-two-term-hom-coordinates). -/
def twoTermHomComponentIso
    (P I Q : CochainComplex (Modules.{t, u} Y R) ℤ)
    (hzero : ∀ k : ℤ, k ≠ -1 → k ≠ 0 → IsZero (Q.X k))
    (eNeg : Q.X (-1) ≅ (𝟙_ (Modules.{t, u} Y R)))
    (eZero : Q.X 0 ≅ (𝟙_ (Modules.{t, u} Y R))) (j p : ℤ) :
    SheafOfModules.homObj (R := R) (P.X p)
        ((((totalTensor Y R).obj I).obj Q).X (p + j)) ≅
      SheafOfModules.homObj (R := R) (P.X p) (I.X (p + (j + 1))) ⊞
        SheafOfModules.homObj (R := R) (P.X p) (I.X (p + j)) :=
  ((SheafOfModules.homFunctor R).obj (op (P.X p))).mapIso
      (twoTermTensorIso Y R I Q hzero eNeg eZero (p + j)) ≪≫
    ((SheafOfModules.homFunctor R).obj (op (P.X p))).mapBiprod _ _ ≪≫
    biprod.mapIso
      (((SheafOfModules.homFunctor R).obj (op (P.X p))).mapIso
          (eqToIso (congrArg I.X (add_assoc p j 1))) ≪≫ parityIso Y R _ p)
      (Iso.refl _)
@[reassoc]
theorem twoTermHomComponentIso_hom_fst
    (P I Q : CochainComplex (Modules.{t, u} Y R) ℤ)
    (hzero : ∀ k : ℤ, k ≠ -1 → k ≠ 0 → IsZero (Q.X k))
    (eNeg : Q.X (-1) ≅ (𝟙_ (Modules.{t, u} Y R)))
    (eZero : Q.X 0 ≅ (𝟙_ (Modules.{t, u} Y R))) (j p : ℤ) :
    (twoTermHomComponentIso Y R P I Q hzero eNeg eZero j p).hom ≫ biprod.fst =
      ((SheafOfModules.homFunctor R).obj (op (P.X p))).map
        ((twoTermTensorIso Y R I Q hzero eNeg eZero (p + j)).hom ≫ biprod.fst ≫
          eqToHom (congrArg I.X (add_assoc p j 1))) ≫ (parityIso Y R _ p).hom := by
  simp only [twoTermHomComponentIso, Iso.trans_hom, biprod.mapIso_hom,
    Functor.mapIso_hom, Category.assoc, biprod.map_fst,
    Functor.mapBiprod_hom, biprod.lift_fst_assoc, Functor.map_comp, eqToIso.hom, Category.assoc]
@[reassoc]
theorem twoTermHomComponentIso_hom_snd
    (P I Q : CochainComplex (Modules.{t, u} Y R) ℤ)
    (hzero : ∀ k : ℤ, k ≠ -1 → k ≠ 0 → IsZero (Q.X k))
    (eNeg : Q.X (-1) ≅ (𝟙_ (Modules.{t, u} Y R)))
    (eZero : Q.X 0 ≅ (𝟙_ (Modules.{t, u} Y R))) (j p : ℤ) :
    (twoTermHomComponentIso Y R P I Q hzero eNeg eZero j p).hom ≫ biprod.snd =
      ((SheafOfModules.homFunctor R).obj (op (P.X p))).map
        ((twoTermTensorIso Y R I Q hzero eNeg eZero (p + j)).hom ≫ biprod.snd) := by
  simp only [twoTermHomComponentIso, Iso.trans_hom, biprod.mapIso_hom,
    Functor.mapIso_hom, Iso.refl_hom, Category.assoc, biprod.map_snd,
    Functor.mapBiprod_hom, Category.comp_id, Functor.map_comp]
  erw [biprod.lift_snd]

/-- The signed finite-coordinate isomorphism on the target Hom term. Only products and
binary products are interchanged; no infinite coproduct passes through a product.
Source: blueprint `lem-coef-integral-hom-reduction.proof.md`, paragraph 1; Stacks 0A8X.
(blueprint: lem-sf-two-term-hom-coordinates). -/
def twoTermHomIso
    (P I Q : CochainComplex (Modules.{t, u} Y R) ℤ)
    (hzero : ∀ k : ℤ, k ≠ -1 → k ≠ 0 → IsZero (Q.X k))
    (eNeg : Q.X (-1) ≅ (𝟙_ (Modules.{t, u} Y R)))
    (eZero : Q.X 0 ≅ (𝟙_ (Modules.{t, u} Y R))) (j : ℤ) :
    (homComplex (R := R) P (((totalTensor Y R).obj I).obj Q)).X j ≅
      (homComplex (R := R) P I).X (j + 1) ⊞ (homComplex (R := R) P I).X j := by
  let J := ((totalTensor Y R).obj I).obj Q
  let A := fun p : ℤ ↦ SheafOfModules.homObj (R := R) (P.X p) (I.X (p + (j + 1)))
  let B := fun p : ℤ ↦ SheafOfModules.homObj (R := R) (P.X p) (I.X (p + j))
  let N := fun p : ℤ ↦ SheafOfModules.homObj (R := R) (P.X p) (J.X (p + j))
  let e (p : ℤ) : N p ≅ A p ⊞ B p :=
    twoTermHomComponentIso Y R P I Q hzero eNeg eZero j p
  exact productBinaryCoordinates
    (Fan.mk _ (fun p : ℤ ↦ homComplexπ (R := R) P I (j + 1) p (p + (j + 1)) rfl))
    (Fan.mk _ (fun p : ℤ ↦ homComplexπ (R := R) P I j p (p + j) rfl))
    (Fan.mk _ (fun p : ℤ ↦ homComplexπ (R := R) P J j p (p + j) rfl))
    (homComplexIsLimit (R := R) P I (j + 1)) (homComplexIsLimit (R := R) P I j)
    (homComplexIsLimit (R := R) P J j) e
@[reassoc]
theorem twoTermHomIso_hom_fst_π
    (P I Q : CochainComplex (Modules.{t, u} Y R) ℤ)
    (hzero : ∀ k : ℤ, k ≠ -1 → k ≠ 0 → IsZero (Q.X k))
    (eNeg : Q.X (-1) ≅ (𝟙_ (Modules.{t, u} Y R)))
    (eZero : Q.X 0 ≅ (𝟙_ (Modules.{t, u} Y R))) (j p : ℤ) :
    (twoTermHomIso Y R P I Q hzero eNeg eZero j).hom ≫ biprod.fst ≫
        homComplexπ (R := R) P I (j + 1) p (p + (j + 1)) rfl =
      homComplexπ (R := R) P (((totalTensor Y R).obj I).obj Q) j p (p + j) rfl ≫
        (twoTermHomComponentIso Y R P I Q hzero eNeg eZero j p).hom ≫ biprod.fst := by
  exact productBinaryCoordinates_hom_fst_proj _ _ _ _ _ _ _ p
@[reassoc]
theorem twoTermHomIso_hom_snd_π
    (P I Q : CochainComplex (Modules.{t, u} Y R) ℤ)
    (hzero : ∀ k : ℤ, k ≠ -1 → k ≠ 0 → IsZero (Q.X k))
    (eNeg : Q.X (-1) ≅ (𝟙_ (Modules.{t, u} Y R)))
    (eZero : Q.X 0 ≅ (𝟙_ (Modules.{t, u} Y R))) (j p : ℤ) :
    (twoTermHomIso Y R P I Q hzero eNeg eZero j).hom ≫ biprod.snd ≫
        homComplexπ (R := R) P I j p (p + j) rfl =
      homComplexπ (R := R) P (((totalTensor Y R).obj I).obj Q) j p (p + j) rfl ≫
        (twoTermHomComponentIso Y R P I Q hzero eNeg eZero j p).hom ≫ biprod.snd := by
  exact productBinaryCoordinates_hom_snd_proj _ _ _ _ _ _ _ p

end WeilConjectures.IntegralHom
