/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerRealizationData
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerCore
import all WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorUnitRepresentatives
import all WeilConjectures.CategoryTheory.Ringed.Slice.RingedSliceScalarUnit
import all WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerComparisonData
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import all WeilConjectures.CategoryTheory.Ringed.Tensor.RingedTensorConstraintCompletion
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import all WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerRealizationData
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel
import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement

/-! # Scalar extension of coherent systems is unital and associative

The whole-system scalar tensorator `ScalarExtensionTower.derivedSigma` is compatible with the
associators and unitors of the published coherent system monoidal structures.

Source: Stacks Project, Tags 03EL and 07A4.
(blueprint: lem-pur-system-scalar-tensor-braiding).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MonoidalCategory
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard pullbackTensorCalculus
  Functor.leftAdjoint Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  integralComparisonSequenceScalarModel
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall

variable (l : ℕ) [Fact l.Prime]
  (E L : Type u) [Field E] [Field L]
  [Algebra (Padic l) E] [Algebra (Padic l) L]
  [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (W : Scheme.{u})

/-- Paste a cochain square through an adjunction unit. -/
private theorem scalarAssoc_adjunction_paste {B D : Type*} [Category B] [Category D]
    {F : B ⥤ D} {G : D ⥤ B} (adj : F ⊣ G)
    {P Q : B} {T V T' V' : D} (a : P ⟶ Q)
    (b : F.obj Q ⟶ T) (c : T ⟶ V)
    (b' : F.obj P ⟶ T') (c' : T' ⟶ V') (d : V' ⟶ V)
    (h : a ≫ adj.unit.app Q ≫ G.map b ≫ G.map c =
      adj.unit.app P ≫ G.map b' ≫ G.map c' ≫ G.map d) :
    F.map a ≫ b ≫ c = b' ≫ c' ≫ d := by
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Functor.map_comp]
  have hu := adj.unit.naturality a
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  rw [← Category.assoc, ← hu]
  simpa only [Category.assoc] using h

/-- Pasting the six pure-section equations requires only function congruence. -/
private theorem scalarAssoc_sectionSquare
    {A B C D E F G H : Type*}
    (σ : A → B) (ηB : B → C) (κB : C → D) (tB : D → H)
    (ηA : A → E) (κA : E → F) (tA : F → G) (τ : G → H)
    (x : A) (b : B) (d : D) (h : H) (f : F) (g : G)
    (hσ : σ x = b) (hκB : κB (ηB b) = d) (htB : tB d = h)
    (hκA : κA (ηA x) = f) (htA : tA f = g) (hτ : τ g = h) :
    tB (κB (ηB (σ x))) = τ (tA (κA (ηA x))) := by
  rw [hσ, hκB, htB, hκA, htA, hτ]

/-- The strict scalar tensorator commutes with cochain reassociation.
Source: Stacks 07A4, with the unsigned reassociation of Tag 06YN.
(blueprint: lem-pur-system-scalar-tensor-braiding).

Proof: transpose both chain maps by the scalar-extension adjunction; detect equality on
local pure triples. Both routes send `x ⊗ y ⊗ z` to the tensor of the three unit images, with
the right parenthesization. -/
theorem scalarSigma_cochain_associativity (P Q N : ScalarExtensionTower.Complex l E W)
    (aY : (ScalarExtensionTower.tensor l E W).obj
        ((ScalarExtensionTower.tensor l E W).obj (P, Q), N) ≅
      (ScalarExtensionTower.tensor l E W).obj (P, (ScalarExtensionTower.tensor l E W).obj (Q, N)))
    (aX : (ScalarExtensionTower.tensor l L W).obj
        ((ScalarExtensionTower.tensor l L W).obj ((ScalarExtensionTower.scalar l E L ι W).obj P,
          (ScalarExtensionTower.scalar l E L ι W).obj Q),
          (ScalarExtensionTower.scalar l E L ι W).obj N) ≅
      (ScalarExtensionTower.tensor l L W).obj ((ScalarExtensionTower.scalar l E L ι W).obj P,
        (ScalarExtensionTower.tensor l L W).obj ((ScalarExtensionTower.scalar l E L ι W).obj Q,
          (ScalarExtensionTower.scalar l E L ι W).obj N)))
    (haY : ∀ (p q r pq qr k : ℤ) (hpq : p + q = pq) (hqr : q + r = qr)
      (hn : pq + r = k) (hn' : p + qr = k) (U : (ℕ × W.ProEt)ᵒᵖ)
      (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) (z : (N.X r).val.obj U),
      (aY.hom.f k).val.app U
        (coefficientTensorGenerator.{u, u + 1, u} (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf.{u, u} l E W)
          ((ScalarExtensionTower.tensor l E W).obj (P, Q)) N pq r k hn U
          (coefficientTensorGenerator.{u, u + 1, u}
            (coefficientSequenceTopology (ProEt.topology W))
            (coefficientSequenceCommRingSheaf.{u, u} l E W) P Q p q pq hpq U x y) z) =
      coefficientTensorGenerator.{u, u + 1, u} (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf.{u, u} l E W) P
        ((ScalarExtensionTower.tensor l E W).obj (Q, N)) p qr k hn' U x
        (coefficientTensorGenerator.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf.{u, u} l E W) Q N q r qr hqr U y z))
    (haX : ∀ (p q r pq qr k : ℤ) (hpq : p + q = pq) (hqr : q + r = qr)
      (hn : pq + r = k) (hn' : p + qr = k) (U : (ℕ × W.ProEt)ᵒᵖ)
      (x : (((ScalarExtensionTower.scalar l E L ι W).obj P).X p).val.obj U)
      (y : (((ScalarExtensionTower.scalar l E L ι W).obj Q).X q).val.obj U)
      (z : (((ScalarExtensionTower.scalar l E L ι W).obj N).X r).val.obj U),
      (aX.hom.f k).val.app U
        (coefficientTensorGenerator.{u, u + 1, u} (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf.{u, u} l L W)
          ((ScalarExtensionTower.tensor l L W).obj ((ScalarExtensionTower.scalar l E L ι W).obj P,
            (ScalarExtensionTower.scalar l E L ι W).obj Q))
          ((ScalarExtensionTower.scalar l E L ι W).obj N) pq r k hn U
          (coefficientTensorGenerator.{u, u + 1, u}
            (coefficientSequenceTopology (ProEt.topology W))
            (coefficientSequenceCommRingSheaf.{u, u} l L W)
            ((ScalarExtensionTower.scalar l E L ι W).obj P)
            ((ScalarExtensionTower.scalar l E L ι W).obj Q) p q pq hpq U x y) z) =
      coefficientTensorGenerator.{u, u + 1, u} (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf.{u, u} l L W)
        ((ScalarExtensionTower.scalar l E L ι W).obj P)
        ((ScalarExtensionTower.tensor l L W).obj ((ScalarExtensionTower.scalar l E L ι W).obj Q,
          (ScalarExtensionTower.scalar l E L ι W).obj N)) p qr k hn' U x
        (coefficientTensorGenerator.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf.{u, u} l L W)
          ((ScalarExtensionTower.scalar l E L ι W).obj Q)
          ((ScalarExtensionTower.scalar l E L ι W).obj N) q r qr hqr U y z)) :
    (ScalarExtensionTower.scalar l E L ι W).map aY.hom ≫
        ((ScalarExtensionTower.comparisons l).sigma E L ι W).hom.app
          (P, (ScalarExtensionTower.tensor l E W).obj (Q, N)) ≫
        (ScalarExtensionTower.tensor l L W).map (Prod.mkHom
          (𝟙 ((ScalarExtensionTower.scalar l E L ι W).obj P))
          (((ScalarExtensionTower.comparisons l).sigma E L ι W).hom.app (Q, N))) =
      ((ScalarExtensionTower.comparisons l).sigma E L ι W).hom.app
          ((ScalarExtensionTower.tensor l E W).obj (P, Q), N) ≫
        (ScalarExtensionTower.tensor l L W).map (Prod.mkHom
          (((ScalarExtensionTower.comparisons l).sigma E L ι W).hom.app (P, Q))
          (𝟙 ((ScalarExtensionTower.scalar l E L ι W).obj N))) ≫ aX.hom := by
  let JW := coefficientSequenceTopology (ProEt.topology W)
  let RE := coefficientSequenceCommRingSheaf.{u, u} l E W
  let RL := coefficientSequenceCommRingSheaf.{u, u} l L W
  let V := ScalarExtensionTower.scalar l E L ι W
  let TY := ScalarExtensionTower.tensor l E W
  let T := ScalarExtensionTower.tensor l L W
  let κ := (ScalarExtensionTower.comparisons l).sigma E L ι W
  let adj := ScalarExtensionTower.scalar_adj l E L ι W
  apply scalarAssoc_adjunction_paste (adj.mapHomologicalComplex (.up ℤ))
  apply CategoryTheory.tensorGenerator_ext₃.{u + 1, u, u} JW RE P Q N
  intro p q r pq k hpq hn U x y z
  have hqr : q + r = q + r := rfl
  have hn' : p + (q + r) = k := by omega
  change ((T.map (Prod.mkHom (𝟙 (V.obj P)) (κ.hom.app (Q, N)))).f k).val.app U
      (((κ.hom.app (P, TY.obj (Q, N))).f k).val.app U
        ((adj.unit.app _).val.app U
          ((aY.hom.f k).val.app U
            (coefficientTensorGenerator.{u, u + 1, u} JW RE (TY.obj (P, Q)) N pq r k hn U
              (coefficientTensorGenerator.{u, u + 1, u} JW RE P Q p q pq hpq U x y) z)))) =
    (aX.hom.f k).val.app U
      (((T.map (Prod.mkHom (κ.hom.app (P, Q)) (𝟙 (V.obj N)))).f k).val.app U
        (((κ.hom.app (TY.obj (P, Q), N)).f k).val.app U
          ((adj.unit.app _).val.app U
            (coefficientTensorGenerator.{u, u + 1, u} JW RE (TY.obj (P, Q)) N pq r k hn U
              (coefficientTensorGenerator.{u, u + 1, u} JW RE P Q p q pq hpq U x y) z))))
  let xp := (adj.unit.app (P.X p)).val.app U x
  let yq := (adj.unit.app (Q.X q)).val.app U y
  let zr := (adj.unit.app (N.X r)).val.app U z
  let gPQ := coefficientTensorGenerator.{u, u + 1, u} JW RE P Q p q pq hpq U x y
  let gQN := coefficientTensorGenerator.{u, u + 1, u} JW RE Q N q r (q + r) hqr U y z
  let gY' := coefficientTensorGenerator.{u, u + 1, u} JW RE P (TY.obj (Q, N))
    p (q + r) k hn' U x gQN
  let gR := coefficientTensorGenerator.{u, u + 1, u} JW RL (V.obj P) (V.obj (TY.obj (Q, N)))
    p (q + r) k hn' U xp ((adj.unit.app ((TY.obj (Q, N)).X (q + r))).val.app U gQN)
  let gL := coefficientTensorGenerator.{u, u + 1, u} JW RL (V.obj (TY.obj (P, Q))) (V.obj N)
    pq r k hn U ((adj.unit.app ((TY.obj (P, Q)).X pq)).val.app U gPQ) zr
  let gPQ' := coefficientTensorGenerator.{u, u + 1, u} JW RL
    (V.obj P) (V.obj Q) p q pq hpq U xp yq
  let gQN' := coefficientTensorGenerator.{u, u + 1, u} JW RL
    (V.obj Q) (V.obj N) q r (q + r) hqr U yq zr
  let gL' := coefficientTensorGenerator.{u, u + 1, u} JW RL
    (T.obj (V.obj P, V.obj Q)) (V.obj N) pq r k hn U gPQ' zr
  let gR' := coefficientTensorGenerator.{u, u + 1, u} JW RL
    (V.obj P) (T.obj (V.obj Q, V.obj N)) p (q + r) k hn' U xp gQN'
  have hκ' : ∀ (A B : ScalarExtensionTower.Complex l E W) (p q k : ℤ) (h : p + q = k)
      (U : (ℕ × W.ProEt)ᵒᵖ) (x : (A.X p).val.obj U) (y : (B.X q).val.obj U),
      ((κ.hom.app (A, B)).f k).val.app U
        ((adj.unit.app _).val.app U
          (coefficientTensorGenerator.{u, u + 1, u} JW RE A B p q k h U x y)) =
      coefficientTensorGenerator.{u, u + 1, u} JW RL (V.obj A) (V.obj B) p q k h U
        ((adj.unit.app (A.X p)).val.app U x)
        ((adj.unit.app (B.X q)).val.app U y) := by
    intro A B p q k h U x y
    subst h
    have h := (ScalarExtensionTower.comparisons l).sigma_formula E L ι W A B p q U 1 x y
    rw [← sequenceScalarAdjunction_unit l E L ι W, ← sequenceScalarAdjunction_unit l E L ι W,
      ← sequenceScalarAdjunction_unit l E L ι W] at h
    exact h
  refine scalarAssoc_sectionSquare
    ((aY.hom.f k).val.app U)
    ((adj.unit.app ((TY.obj (P, TY.obj (Q, N))).X k)).val.app U)
    (((κ.hom.app (P, TY.obj (Q, N))).f k).val.app U)
    (((T.map (Prod.mkHom (𝟙 (V.obj P)) (κ.hom.app (Q, N)))).f k).val.app U)
    ((adj.unit.app ((TY.obj (TY.obj (P, Q), N)).X k)).val.app U)
    (((κ.hom.app (TY.obj (P, Q), N)).f k).val.app U)
    (((T.map (Prod.mkHom (κ.hom.app (P, Q)) (𝟙 (V.obj N)))).f k).val.app U)
    ((aX.hom.f k).val.app U)
    _ gY' gR gR' gL gL' ?_ ?_ ?_ ?_ ?_ ?_
  · exact haY p q r pq (q + r) k hpq hqr hn hn' U x y z
  · exact hκ' P (TY.obj (Q, N)) p (q + r) k hn' U x gQN
  · have hm := CategoryTheory.ScalarHomTensor.tensor_generator_map.{u + 1, u, u}
      (𝟙 (V.obj P)) (κ.hom.app (Q, N)) p (q + r) k hn' U xp
      ((adj.unit.app ((TY.obj (Q, N)).X (q + r))).val.app U gQN)
    simp only [HomologicalComplex.id_f, SheafOfModules.id_val,
      PresheafOfModules.id_app] at hm
    exact hm.trans (congrArg (fun w ↦ coefficientTensorGenerator.{u, u + 1, u}
      JW RL (V.obj P) (T.obj (V.obj Q, V.obj N)) p (q + r) k hn' U xp w)
      (hκ' Q N q r (q + r) hqr U y z))
  · exact hκ' (TY.obj (P, Q)) N pq r k hn U gPQ z
  · have hm := CategoryTheory.ScalarHomTensor.tensor_generator_map.{u + 1, u, u}
      (κ.hom.app (P, Q)) (𝟙 (V.obj N)) pq r k hn U
      ((adj.unit.app ((TY.obj (P, Q)).X pq)).val.app U gPQ) zr
    simp only [HomologicalComplex.id_f, SheafOfModules.id_val,
      PresheafOfModules.id_app] at hm
    exact hm.trans (congrArg (fun w ↦ coefficientTensorGenerator.{u, u + 1, u}
      JW RL (T.obj (V.obj P, V.obj Q)) (V.obj N) pq r k hn U w zr)
      (hκ' P Q p q pq hpq U x y))
  · exact haX p q r pq (q + r) k hpq hqr hn hn' U xp yq zr

private theorem scalarAssoc_localization_paste
    {C B D A : Type*} [Category C] [Category B] [Category D] [Category A]
    (F : C ⥤ B) (G : D ⥤ A) (U : B ⥤ A) (V : C ⥤ D)
    (e : F ⋙ U ⟶ V ⋙ G) {P Q : C} {R S R' S' : D}
    (a : P ⟶ Q) (b : V.obj Q ⟶ R) (c : R ⟶ S)
    (d : V.obj P ⟶ R') (j : R' ⟶ S') (a' : S' ⟶ S)
    (h : V.map a ≫ b ≫ c = d ≫ j ≫ a') :
    U.map (F.map a) ≫ (e.app Q ≫ G.map b ≫ G.map c) =
      (e.app P ≫ G.map d ≫ G.map j) ≫ G.map a' := by
  have he := e.naturality a
  dsimp only [Functor.comp_map] at he
  simp only [← Category.assoc]
  rw [he]
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun f ↦ e.app P ≫ G.map f) h

/-- Categorical pasting, from naturality and cancellation.
Source: Stacks 07A4
(blueprint: lem-pur-completed-pullback-tensor-associativity-representatives). -/
private theorem scalarAssoc_left_square {B : Type*} [Category B] [MonoidalCategory B]
    {A : Type*} [Category A] [MonoidalCategory A]
    (F : B ⥤ A)
    (μ : MonoidalCategory.tensor B ⋙ F ≅ (F.prod F) ⋙ MonoidalCategory.tensor A)
    {X Y Z V W : B} {X' Y' Z' V' W' : A}
    (i : V ⟶ X ⊗ Y) (j : W ⟶ V ⊗ Z)
    (eX : F.obj X ⟶ X') (eY : F.obj Y ⟶ Y') (eZ : F.obj Z ⟶ Z')
    (eV : F.obj V ⟶ V') (eW : F.obj W ⟶ W')
    (i' : V' ⟶ X' ⊗ Y') (j' : W' ⟶ V' ⊗ Z')
    (hi : F.map i ≫ μ.hom.app (X, Y) ≫ (eX ⊗ₘ eY) = eV ≫ i')
    (hj : F.map j ≫ μ.hom.app (V, Z) ≫ (eV ⊗ₘ eZ) = eW ≫ j') :
    F.map (j ≫ (i ▷ Z)) ≫ μ.hom.app (X ⊗ Y, Z) ≫
        (μ.hom.app (X, Y) ▷ F.obj Z) ≫ ((eX ⊗ₘ eY) ⊗ₘ eZ) =
      eW ≫ j' ≫ (i' ▷ Z') := by
  dsimp only [Functor.comp_obj, Functor.prod_obj] at *
  have hn := μ.hom.naturality (X := (V, Z)) (Y := (X ⊗ Y, Z)) (i, 𝟙 Z)
  simp only [Functor.comp_map, Functor.prod_map, tensor_map, F.map_id, tensorHom_id] at hn
  calc
    _ = F.map j ≫ μ.hom.app (V, Z) ≫
        ((F.map i ≫ μ.hom.app (X, Y) ≫ (eX ⊗ₘ eY)) ⊗ₘ eZ) := by
      simp only [F.map_comp, Category.assoc]
      rw [reassoc_of% hn]
      simp only [← tensorHom_id, tensorHom_comp_tensorHom,
        Category.id_comp]
      erw [Category.id_comp]
    _ = F.map j ≫ μ.hom.app (V, Z) ≫ ((eV ≫ i') ⊗ₘ eZ) := by rw [hi]
    _ = (F.map j ≫ μ.hom.app (V, Z) ≫ (eV ⊗ₘ eZ)) ≫ (i' ▷ Z') := by
      simp only [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id, Category.assoc]
    _ = _ := by rw [hj]; simp only [Category.assoc]

/-- Categorical pasting, from naturality and cancellation.
Source: Stacks 07A4
(blueprint: lem-pur-completed-pullback-tensor-associativity-representatives). -/
private theorem scalarAssoc_right_square {B : Type*} [Category B] [MonoidalCategory B]
    {A : Type*} [Category A] [MonoidalCategory A]
    (F : B ⥤ A)
    (μ : MonoidalCategory.tensor B ⋙ F ≅ (F.prod F) ⋙ MonoidalCategory.tensor A)
    {X Y Z V W : B} {X' Y' Z' V' W' : A}
    (i : V ⟶ Y ⊗ Z) (j : W ⟶ X ⊗ V)
    (eX : F.obj X ⟶ X') (eY : F.obj Y ⟶ Y') (eZ : F.obj Z ⟶ Z')
    (eV : F.obj V ⟶ V') (eW : F.obj W ⟶ W')
    (i' : V' ⟶ Y' ⊗ Z') (j' : W' ⟶ X' ⊗ V')
    (hi : F.map i ≫ μ.hom.app (Y, Z) ≫ (eY ⊗ₘ eZ) = eV ≫ i')
    (hj : F.map j ≫ μ.hom.app (X, V) ≫ (eX ⊗ₘ eV) = eW ≫ j') :
    F.map (j ≫ (X ◁ i)) ≫ μ.hom.app (X, Y ⊗ Z) ≫
        (F.obj X ◁ μ.hom.app (Y, Z)) ≫ (eX ⊗ₘ (eY ⊗ₘ eZ)) =
      eW ≫ j' ≫ (X' ◁ i') := by
  dsimp only [Functor.comp_obj, Functor.prod_obj] at *
  have hn := μ.hom.naturality (X := (X, V)) (Y := (X, Y ⊗ Z)) (𝟙 X, i)
  simp only [Functor.comp_map, Functor.prod_map, tensor_map, F.map_id, id_tensorHom] at hn
  calc
    _ = F.map j ≫ μ.hom.app (X, V) ≫
        (eX ⊗ₘ (F.map i ≫ μ.hom.app (Y, Z) ≫ (eY ⊗ₘ eZ))) := by
      simp only [F.map_comp, Category.assoc]
      rw [reassoc_of% hn]
      simp only [← id_tensorHom, tensorHom_comp_tensorHom,
        Category.id_comp]
      erw [Category.id_comp]
    _ = F.map j ≫ μ.hom.app (X, V) ≫ (eX ⊗ₘ (eV ≫ i')) := by rw [hi]
    _ = (F.map j ≫ μ.hom.app (X, V) ≫ (eX ⊗ₘ eV)) ≫ (X' ◁ i') := by
      simp only [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id, Category.assoc]
    _ = _ := by rw [hj]; simp only [Category.assoc]

/-- Categorical pasting, from naturality and cancellation.
Source: Stacks 07A4
(blueprint: lem-pur-completed-pullback-tensor-associativity-representatives). -/
private theorem scalarAssoc_transport
    {B : Type*} [Category B] [MonoidalCategory B]
    {A : Type*} [Category A] [MonoidalCategory A]
    (F : B ⥤ A)
    (μ : MonoidalCategory.tensor B ⋙ F ≅ (F.prod F) ⋙ MonoidalCategory.tensor A)
    {X Y Z V W : B} {X' Y' Z' V' W' : A}
    (l : V ≅ (X ⊗ Y) ⊗ Z) (r : W ≅ X ⊗ (Y ⊗ Z)) (a : V ⟶ W)
    (l' : V' ⟶ (X' ⊗ Y') ⊗ Z') (r' : W' ⟶ X' ⊗ (Y' ⊗ Z')) (a' : V' ⟶ W')
    (eX : F.obj X ≅ X') (eY : F.obj Y ≅ Y') (eZ : F.obj Z ≅ Z')
    (eV : F.obj V ⟶ V') (eW : F.obj W ⟶ W')
    (hB : l.hom ≫ (α_ X Y Z).hom = a ≫ r.hom)
    (hA : l' ≫ (α_ X' Y' Z').hom = a' ≫ r')
    (hL : F.map l.hom ≫ μ.hom.app (X ⊗ Y, Z) ≫
      (μ.hom.app (X, Y) ▷ F.obj Z) ≫ ((eX.hom ⊗ₘ eY.hom) ⊗ₘ eZ.hom) = eV ≫ l')
    (hR : F.map r.hom ≫ μ.hom.app (X, Y ⊗ Z) ≫
      (F.obj X ◁ μ.hom.app (Y, Z)) ≫ (eX.hom ⊗ₘ (eY.hom ⊗ₘ eZ.hom)) = eW ≫ r')
    (hC : F.map a ≫ eW = eV ≫ a') :
    F.map (α_ X Y Z).hom ≫ μ.hom.app (X, Y ⊗ Z) ≫
        (F.obj X ◁ μ.hom.app (Y, Z)) =
      μ.hom.app (X ⊗ Y, Z) ≫ (μ.hom.app (X, Y) ▷ F.obj Z) ≫
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom := by
  apply (cancel_epi (F.map l.hom)).1
  apply (cancel_mono (eX.hom ⊗ₘ (eY.hom ⊗ₘ eZ.hom))).1
  calc
    _ = F.map a ≫ F.map r.hom ≫ μ.hom.app (X, Y ⊗ Z) ≫
        (F.obj X ◁ μ.hom.app (Y, Z)) ≫ (eX.hom ⊗ₘ (eY.hom ⊗ₘ eZ.hom)) := by
      rw [← F.map_comp_assoc, hB, F.map_comp]
      simp only [Category.assoc]
    _ = F.map a ≫ eW ≫ r' := by rw [hR]
    _ = eV ≫ a' ≫ r' := by rw [reassoc_of% hC]
    _ = eV ≫ l' ≫ (α_ X' Y' Z').hom := by rw [hA]
    _ = F.map l.hom ≫ μ.hom.app (X ⊗ Y, Z) ≫
        (μ.hom.app (X, Y) ▷ F.obj Z) ≫ ((eX.hom ⊗ₘ eY.hom) ⊗ₘ eZ.hom) ≫
          (α_ X' Y' Z').hom := by rw [reassoc_of% hL]
    _ = _ := by
      erw [associator_naturality]
      simp only [Category.assoc]
      rfl

/-- The selected calculus retains the system normalization from its resolution model.
Source: Stacks 07A4 and 0941 (blueprint: lem-pur-system-scalar-tensor-braiding). -/
private theorem scalar_systemTensorCoherence (D : Type u) [Field D] [Algebra (Padic l) D]
    [FiniteDimensional (Padic l) D] (W : Scheme.{u}) :
    ∃ β : @SymmetricCategory (coefficientSequenceDerived l D W) _
      (pullbackTensorCalculus l D W).systemClosed.monoidal,
      Nonempty (RingedDerivedTensorCoherence
        (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf l D W)
        (pullbackTensorCalculus l D W).systemClosed
        (pullbackTensorCalculus l D W).systemTensorModel β) := by
  unfold pullbackTensorCalculus
  exact (coefficientDerivedSystemEvaluationCalculus l D W).choose_spec.some.systemTensorCoherence

/-- Total tensors of good complexes are good. -/
private theorem scalarAssoc_tensor_good (D : Type u) [Field D] [Algebra (Padic l) D]
    [FiniteDimensional (Padic l) D] (W : Scheme.{u}) (P Q : ScalarExtensionTower.Complex l D W)
    (hP : ScalarExtensionTower.Good l D W P) (hQ : ScalarExtensionTower.Good l D W Q) :
    ScalarExtensionTower.Good l D W ((ScalarExtensionTower.tensor l D W).obj (P, Q)) :=
  ⟨coefficientTotalTensor_isKFlat.{u, u + 1, u} _ _ P Q hP.1 hQ.1, by
    rw [show ScalarExtensionTower.tensor l D W = SheafOfModules.KFlatTotalTensorModel.total
      (coefficientSequenceCommRingSheaf.{u, u} l D W) from rfl]
    exact (SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model
      (coefficientSequenceCommRingSheaf.{u, u} l D W) P Q hP.1 hQ.1 hP.2 hQ.2).2.1⟩

/-- Naturality of a tensor comparison with its right input fixed. -/
private theorem scalarAssoc_tensor_naturality_right
    {C D : Type*} [Category C] [Category D] [MonoidalCategory D]
    (F : C ⥤ D) (T : C × C ⥤ D) (μ : T ≅ F.prod F ⋙ MonoidalCategory.tensor D)
    {X X' : C} (f : X ⟶ X') (Y : C) :
    T.map (f, 𝟙 Y) ≫ μ.hom.app (X', Y) =
      μ.hom.app (X, Y) ≫ (F.map f ▷ F.obj Y) := by
  have h := μ.hom.naturality (X := (X, Y)) (Y := (X', Y)) (f, 𝟙 Y)
  simp only [Functor.comp_map, Functor.prod_map, tensor_map, F.map_id] at h
  erw [tensorHom_id] at h
  exact h

/-- Naturality of a tensor comparison with its left input fixed. -/
private theorem scalarAssoc_tensor_naturality_left
    {C D : Type*} [Category C] [Category D] [MonoidalCategory D]
    (F : C ⥤ D) (T : C × C ⥤ D) (μ : T ≅ F.prod F ⋙ MonoidalCategory.tensor D)
    (X : C) {Y Y' : C} (f : Y ⟶ Y') :
    T.map (𝟙 X, f) ≫ μ.hom.app (X, Y') =
      μ.hom.app (X, Y) ≫ (F.obj X ◁ F.map f) := by
  have h := μ.hom.naturality (X := (X, Y)) (Y := (X, Y')) (𝟙 X, f)
  simp only [Functor.comp_map, Functor.prod_map, tensor_map, F.map_id] at h
  erw [id_tensorHom] at h
  exact h

/-- Normalize an associator square along the two chosen tensor-model isomorphisms. -/
private theorem scalarAssoc_model_associator
    {D : Type*} [Category D] [MonoidalCategory D]
    {X Y Z XY YZ L R : D}
    (iL bL : L ≅ XY ⊗ Z) (iR bR : R ≅ X ⊗ YZ)
    (bPQ : XY ≅ X ⊗ Y) (bQN : YZ ≅ Y ⊗ Z) (a : L ⟶ R)
    (hL : iL = bL) (hR : iR = bR)
    (h : iL.hom ≫ (bPQ.hom ⊗ₘ 𝟙 Z) ≫ (α_ X Y Z).hom =
      a ≫ iR.hom ≫ (𝟙 X ⊗ₘ bQN.hom)) :
    (bL ≪≫ whiskerRightIso bPQ Z).hom ≫ (α_ X Y Z).hom =
      a ≫ (bR ≪≫ whiskerLeftIso X bQN).hom := by
  subst bL bR
  erw [tensorHom_id, id_tensorHom] at h
  simpa only [Iso.trans_hom, whiskerRightIso_hom, whiskerLeftIso_hom, Category.assoc] using h

section Representatives
attribute [local implicit_reducible] coefficientSequenceInternalHom coefficientSequenceHasDerived
  CoefficientClosedStructure.tensor
attribute [local irreducible]
  DerivedCategory _root_.instCategoryDerivedCategory DerivedCategory.Q
  SheafOfModules.monoidalCategory CochainComplex.IsKFlatIndependentCoefficients
  derivedInternalHomOfUniverses coefficientTotalTensor Functor.mapHomologicalComplex

/-- The scalar tensorator's normalization with the fixed good scalar representatives. -/
private theorem scalarAssoc_tensor_normalization (P Q : ScalarExtensionTower.Complex l E W)
    (hP : ScalarExtensionTower.Good l E W P) (hQ : ScalarExtensionTower.Good l E W Q) :
    let SE := pullbackTensorCalculus l E W
    let SL := pullbackTensorCalculus l L W
    let V := ScalarExtensionTower.scalar l E L ι W
    let δ := integralComparisonSequenceScalarModel.{u, u} l E L ι W
    (integralComparisonDerivedSequenceScalar l E L ι W).map
        (SE.systemTensorModel.iso _ _ _ P Q hP.1 hQ.1).hom ≫
      (ScalarExtensionTower.derivedSigma l E L ι W SE SL).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      SL.systemClosed.tensor.map (Prod.mkHom (δ.ε.app P) (δ.ε.app Q)) =
    δ.ε.app ((ScalarExtensionTower.tensor l E W).obj (P, Q)) ≫
      DerivedCategory.Q.map (((ScalarExtensionTower.comparisons l).sigma E L ι W).hom.app
        (P, Q)) ≫
      (SL.systemTensorModel.iso _ _ _ (V.obj P) (V.obj Q)
        (ScalarExtensionTower.scalar_good l E L ι W P hP).1
        (ScalarExtensionTower.scalar_good l E L ι W Q hQ).1).hom := by
  have h := (ScalarExtensionTower.derivedSigma_existsUnique l E L ι W
    (pullbackTensorCalculus l E W) (pullbackTensorCalculus l L W)).exists.choose_spec
  obtain ⟨_, _, h⟩ := h P Q hP hQ
  exact h

/-- Associativity of the scalar tensorator on three good representatives.
Source: Stacks 07A4, total tensor construction (blueprint: lem-pur-system-scalar-tensor-braiding).
Proof: insert the cochain normalizations of the scalar tensorator, of the tensor models and of
the system associators; the strict scalar tensorator is associative on cochains. -/
private theorem scalarAssoc_representatives (A B C : ScalarExtensionTower.Complex l E W)
    (hA : ScalarExtensionTower.Good l E W A) (hB : ScalarExtensionTower.Good l E W B)
    (hC : ScalarExtensionTower.Good l E W C) :
    let M := DerivedCategory.Q.obj A
    let N := DerivedCategory.Q.obj B
    let P := DerivedCategory.Q.obj C
    (integralComparisonDerivedSequenceScalar l E L ι W).map
      ((pullbackTensorCalculus l E W).systemClosed.monoidal.associator M N P).hom ≫
      (ScalarExtensionTower.derivedSigma l E L ι W
        (pullbackTensorCalculus l E W) (pullbackTensorCalculus l L W)).hom.app
        (M, (pullbackTensorCalculus l E W).systemClosed.tensor.obj (N, P)) ≫
      (pullbackTensorCalculus l L W).systemClosed.tensor.map
        (Prod.mkHom (𝟙 _) ((ScalarExtensionTower.derivedSigma l E L ι W
          (pullbackTensorCalculus l E W) (pullbackTensorCalculus l L W)).hom.app (N, P))) =
    (ScalarExtensionTower.derivedSigma l E L ι W
        (pullbackTensorCalculus l E W) (pullbackTensorCalculus l L W)).hom.app
        ((pullbackTensorCalculus l E W).systemClosed.tensor.obj (M, N), P) ≫
      (pullbackTensorCalculus l L W).systemClosed.tensor.map
        (Prod.mkHom ((ScalarExtensionTower.derivedSigma l E L ι W
          (pullbackTensorCalculus l E W) (pullbackTensorCalculus l L W)).hom.app (M, N)) (𝟙 _)) ≫
      ((pullbackTensorCalculus l L W).systemClosed.monoidal.associator
        ((integralComparisonDerivedSequenceScalar l E L ι W).obj M)
        ((integralComparisonDerivedSequenceScalar l E L ι W).obj N)
        ((integralComparisonDerivedSequenceScalar l E L ι W).obj P)).hom := by
  let P := A
  let Q := B
  let N := C
  have hPg := hA
  have hQg := hB
  have hNg := hC
  have hP := hA.1
  have hQ := hB.1
  have hN := hC.1
  let J := coefficientSequenceTopology (ProEt.topology W)
  let R := coefficientSequenceCommRingSheaf.{u, u} l E W
  let J' := coefficientSequenceTopology (ProEt.topology W)
  let R' := coefficientSequenceCommRingSheaf.{u, u} l L W
  let δ := integralComparisonSequenceScalarModel.{u, u} l E L ι W
  let H := integralComparisonDerivedSequenceScalar l E L ι W
  let SB := (pullbackTensorCalculus l E W).systemClosed
  let TB := (pullbackTensorCalculus l E W).systemTensorModel
  let SA := (pullbackTensorCalculus l L W).systemClosed
  let TA := (pullbackTensorCalculus l L W).systemTensorModel
  let μ := ScalarExtensionTower.derivedSigma l E L ι W
    (pullbackTensorCalculus l E W) (pullbackTensorCalculus l L W)
  let chain := (ScalarExtensionTower.comparisons l).sigma E L ι W
  have hCB := scalar_systemTensorCoherence l E W
  have hCA := scalar_systemTensorCoherence l L W
  obtain ⟨βB, ⟨cB⟩⟩ := hCB
  obtain ⟨βA, ⟨cA⟩⟩ := hCA
  let := SB.monoidal
  let : MonoidalCategoryStruct (coefficientSequenceDerived l E W) :=
    SB.monoidal.toMonoidalCategoryStruct
  let := SA.monoidal
  let : MonoidalCategoryStruct (coefficientSequenceDerived l L W) :=
    SA.monoidal.toMonoidalCategoryStruct
  change H.map (α_ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
      (DerivedCategory.Q.obj N)).hom ≫
      μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q ⊗ DerivedCategory.Q.obj N) ≫
      (𝟙 (H.obj (DerivedCategory.Q.obj P)) ⊗ₘ
        μ.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj N)) =
    μ.hom.app (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q, DerivedCategory.Q.obj N) ≫
      (μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ⊗ₘ
        𝟙 (H.obj (DerivedCategory.Q.obj N))) ≫
      (α_ (H.obj (DerivedCategory.Q.obj P))
        (H.obj (DerivedCategory.Q.obj Q))
        (H.obj (DerivedCategory.Q.obj N))).hom
  erw [id_tensorHom, tensorHom_id]
  let V := ScalarExtensionTower.scalar l E L ι W
  let B := coefficientTotalTensor.{u, u + 1, u} J R
  let A := coefficientTotalTensor.{u, u + 1, u} J' R'
  let PQ := B.obj (P, Q)
  let QN := B.obj (Q, N)
  have hPQg := scalarAssoc_tensor_good l E W P Q hPg hQg
  have hQNg := scalarAssoc_tensor_good l E W Q N hQg hNg
  have hPQ := hPQg.1
  have hQN := hQNg.1
  have hUPg := ScalarExtensionTower.scalar_good l E L ι W P hPg
  have hUQg := ScalarExtensionTower.scalar_good l E L ι W Q hQg
  have hUNg := ScalarExtensionTower.scalar_good l E L ι W N hNg
  have hUPQ := (ScalarExtensionTower.scalar_good l E L ι W PQ hPQg).1
  have hUQN := (ScalarExtensionTower.scalar_good l E L ι W QN hQNg).1
  have hUP := hUPg.1
  have hUQ := hUQg.1
  have hUN := hUNg.1
  have hAPQ := coefficientTotalTensor_isKFlat.{u, u + 1, u} J' R' (V.obj P) (V.obj Q) hUP hUQ
  have hAQN := coefficientTotalTensor_isKFlat.{u, u + 1, u} J' R' (V.obj Q) (V.obj N) hUQ hUN
  obtain ⟨aB, haB, heB⟩ := cB.associator_model P Q N hP hQ hN
  obtain ⟨aA, haA, heA⟩ := cA.associator_model (V.obj P) (V.obj Q) (V.obj N) hUP hUQ hUN
  have hc := scalarSigma_cochain_associativity l E L ι W P Q N aB aA haB haA
  let bPQ := TB.iso J R SB P Q hP hQ
  let bQN := TB.iso J R SB Q N hQ hN
  let bL := TB.iso J R SB PQ N hPQ hN
  let bR := TB.iso J R SB P QN hP hQN
  let aPQ := TA.iso J' R' SA (V.obj P) (V.obj Q) hUP hUQ
  let aQN := TA.iso J' R' SA (V.obj Q) (V.obj N) hUQ hUN
  let aL := TA.iso J' R' SA (A.obj (V.obj P, V.obj Q)) (V.obj N) hAPQ hUN
  let aR := TA.iso J' R' SA (V.obj P) (A.obj (V.obj Q, V.obj N)) hUP hAQN
  let aL₀ := TA.iso J' R' SA (V.obj PQ) (V.obj N) hUPQ hUN
  let aR₀ := TA.iso J' R' SA (V.obj P) (V.obj QN) hUP hUQN
  let lB := bL ≪≫ whiskerRightIso bPQ (DerivedCategory.Q.obj N)
  let rB := bR ≪≫ whiskerLeftIso (DerivedCategory.Q.obj P) bQN
  let lA := aL ≪≫ whiskerRightIso aPQ (DerivedCategory.Q.obj (V.obj N))
  let rA := aR ≪≫ whiskerLeftIso (DerivedCategory.Q.obj (V.obj P)) aQN
  let e : DerivedCategory.Q ⋙ H ⟶ V ⋙ DerivedCategory.Q := δ.ε
  let tPQ : DerivedCategory.Q.obj (V.obj PQ) ⟶
      DerivedCategory.Q.obj (A.obj (V.obj P, V.obj Q)) :=
    DerivedCategory.Q.map (chain.hom.app (P, Q))
  let tQN : DerivedCategory.Q.obj (V.obj QN) ⟶
      DerivedCategory.Q.obj (A.obj (V.obj Q, V.obj N)) :=
    DerivedCategory.Q.map (chain.hom.app (Q, N))
  let tL : DerivedCategory.Q.obj (V.obj (B.obj (PQ, N))) ⟶
      DerivedCategory.Q.obj (A.obj (V.obj PQ, V.obj N)) :=
    DerivedCategory.Q.map (chain.hom.app (PQ, N))
  let tR : DerivedCategory.Q.obj (V.obj (B.obj (P, QN))) ⟶
      DerivedCategory.Q.obj (A.obj (V.obj P, V.obj QN)) :=
    DerivedCategory.Q.map (chain.hom.app (P, QN))
  let eL := e.app (B.obj (PQ, N)) ≫ tL ≫
    DerivedCategory.Q.map (A.map (X := (V.obj PQ, V.obj N))
      (Y := (A.obj (V.obj P, V.obj Q), V.obj N))
      (chain.hom.app (P, Q), 𝟙 (V.obj N)))
  let eR := e.app (B.obj (P, QN)) ≫ tR ≫
    DerivedCategory.Q.map (A.map (X := (V.obj P, V.obj QN))
      (Y := (V.obj P, A.obj (V.obj Q, V.obj N)))
      (𝟙 (V.obj P), chain.hom.app (Q, N)))
  have hB : lB.hom ≫ (α_ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
        (DerivedCategory.Q.obj N)).hom = DerivedCategory.Q.map aB.hom ≫ rB.hom := by
    exact scalarAssoc_model_associator _ bL _ bR bPQ bQN (DerivedCategory.Q.map aB.hom)
      (cB.tensorIso_both PQ N hPQ hN) (cB.tensorIso_both P QN hP hQN) heB
  have hA : lA.hom ≫ (α_ (DerivedCategory.Q.obj (V.obj P))
        (DerivedCategory.Q.obj (V.obj Q)) (DerivedCategory.Q.obj (V.obj N))).hom =
      DerivedCategory.Q.map aA.hom ≫ rA.hom := by
    exact scalarAssoc_model_associator _ aL _ aR aPQ aQN (DerivedCategory.Q.map aA.hom)
      (cA.tensorIso_both (A.obj (V.obj P, V.obj Q)) (V.obj N) hAPQ hUN)
      (cA.tensorIso_both (V.obj P) (A.obj (V.obj Q, V.obj N)) hUP hAQN) heA
  have hmPQ := scalarAssoc_tensor_normalization l E L ι W P Q hPg hQg
  have hmQN := scalarAssoc_tensor_normalization l E L ι W Q N hQg hNg
  have hmL := scalarAssoc_tensor_normalization l E L ι W PQ N hPQg hNg
  have hmR := scalarAssoc_tensor_normalization l E L ι W P QN hPg hQNg
  change H.map bPQ.hom ≫ μ.hom.app (_, _) ≫
    ((e.app P) ⊗ₘ (e.app Q)) = e.app _ ≫ tPQ ≫ aPQ.hom at hmPQ
  change H.map bQN.hom ≫ μ.hom.app (_, _) ≫
    ((e.app Q) ⊗ₘ (e.app N)) = e.app _ ≫ tQN ≫ aQN.hom at hmQN
  change H.map bL.hom ≫ μ.hom.app (_, _) ≫
    ((e.app PQ) ⊗ₘ (e.app N)) = e.app _ ≫ tL ≫ aL₀.hom at hmL
  change H.map bR.hom ≫ μ.hom.app (_, _) ≫
    ((e.app P) ⊗ₘ (e.app QN)) = e.app _ ≫ tR ≫ aR₀.hom at hmR
  have hnL : DerivedCategory.Q.map (A.map (chain.hom.app (P, Q), 𝟙 (V.obj N))) ≫
      aL.hom = aL₀.hom ≫ (tPQ ▷ DerivedCategory.Q.obj (V.obj N)) :=
    scalarAssoc_tensor_naturality_right _ _ TA.comparison
      (X := ⟨V.obj PQ, hUPQ⟩) (X' := ⟨A.obj (V.obj P, V.obj Q), hAPQ⟩)
      (ObjectProperty.homMk (chain.hom.app (P, Q))) ⟨V.obj N, hUN⟩
  have hnR : DerivedCategory.Q.map (A.map (𝟙 (V.obj P), chain.hom.app (Q, N))) ≫
      aR.hom = aR₀.hom ≫ (DerivedCategory.Q.obj (V.obj P) ◁ tQN) :=
    scalarAssoc_tensor_naturality_left _ _ TA.comparison
      (Y := ⟨V.obj QN, hUQN⟩) (Y' := ⟨A.obj (V.obj Q, V.obj N), hAQN⟩)
      ⟨V.obj P, hUP⟩ (ObjectProperty.homMk (chain.hom.app (Q, N)))
  have hL₀ := scalarAssoc_left_square
    H μ bPQ.hom bL.hom
    (e.app P) (e.app Q) (e.app N) (e.app PQ)
    (e.app (B.obj (PQ, N))) (tPQ ≫ aPQ.hom) (tL ≫ aL₀.hom) hmPQ hmL
  have hR₀ := scalarAssoc_right_square
    H μ bQN.hom bR.hom
    (e.app P) (e.app Q) (e.app N) (e.app QN)
    (e.app (B.obj (P, QN))) (tQN ≫ aQN.hom) (tR ≫ aR₀.hom) hmQN hmR
  have hL : H.map lB.hom ≫
      μ.hom.app (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q,
        DerivedCategory.Q.obj N) ≫
      (μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ▷
        H.obj (DerivedCategory.Q.obj N)) ≫
      (((e.app P) ⊗ₘ (e.app Q)) ⊗ₘ (e.app N)) = eL ≫ lA.hom := by
    calc
      _ = e.app (B.obj (PQ, N)) ≫ (tL ≫ aL₀.hom) ≫
          ((tPQ ≫ aPQ.hom) ▷ DerivedCategory.Q.obj (V.obj N)) := hL₀
      _ = _ := by
        simp only [comp_whiskerRight, Category.assoc]
        erw [← reassoc_of% hnL]
        simp only [eL, lA, Iso.trans_hom, whiskerRightIso_hom, Category.assoc]
  have hR : H.map rB.hom ≫
      μ.hom.app (DerivedCategory.Q.obj P,
        DerivedCategory.Q.obj Q ⊗ DerivedCategory.Q.obj N) ≫
      (H.obj (DerivedCategory.Q.obj P) ◁
        μ.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj N)) ≫
      ((e.app P) ⊗ₘ ((e.app Q) ⊗ₘ (e.app N))) = eR ≫ rA.hom := by
    calc
      _ = e.app (B.obj (P, QN)) ≫ (tR ≫ aR₀.hom) ≫
          (DerivedCategory.Q.obj (V.obj P) ◁ (tQN ≫ aQN.hom)) := hR₀
      _ = _ := by
        simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
        erw [← reassoc_of% hnR]
        simp only [eR, rA, Iso.trans_hom, whiskerLeftIso_hom, Category.assoc]
  have hC := scalarAssoc_localization_paste DerivedCategory.Q DerivedCategory.Q
    H V e _ _ _ _ _ _ hc
  refine scalarAssoc_transport
    H μ lB rB (DerivedCategory.Q.map aB.hom)
    lA.hom rA.hom (DerivedCategory.Q.map aA.hom) (@asIso _ _ _ _ (e.app P) (δ.computes P hP))
    (@asIso _ _ _ _ (e.app Q) (δ.computes Q hQ))
    (@asIso _ _ _ _ (e.app N) (δ.computes N hN)) eL eR ?_ ?_ ?_ ?_ ?_
  · exact hB
  · exact hA
  · exact hL
  · exact hR
  · exact hC

end Representatives


/-- The normalized whole-system scalar tensorator is associative.

Source: Stacks 07A4, total tensor construction; the scalar calculation of
lem-pur-system-scalar-tensor-braiding.
(blueprint: lem-pur-system-scalar-tensor-braiding).

Proof plan: take simultaneous flat-term K-flat representatives. By `DerivedSigmaModel` the
derived scalar tensorator is the localization of the strict scalar tensorator, conjugated by
the fixed tensor models and scalar counits; the system associators are the localizations of the
total reassociation maps with the same models. On a homogeneous local tensor both strict routes
send `c ⊗ ((x ⊗ y) ⊗ z)` to `(c x) ⊗ (y ⊗ z)` without a sign. These generators span the
sheafified total tensors, so the chain maps agree; localize and extend by naturality. -/
theorem systemScalarTensorAssociativity
    (M N P : coefficientSequenceDerived l E W) :
    let H := integralComparisonDerivedSequenceScalar l E L ι W
    let σ := ScalarExtensionTower.derivedSigma l E L ι W
      (pullbackTensorCalculus l E W) (pullbackTensorCalculus l L W)
    H.map ((pullbackTensorCalculus l E W).systemClosed.monoidal.associator M N P).hom ≫
      σ.hom.app (M, (pullbackTensorCalculus l E W).systemClosed.tensor.obj (N, P)) ≫
      (pullbackTensorCalculus l L W).systemClosed.tensor.map
        (Prod.mkHom (𝟙 _) (σ.hom.app (N, P))) =
    σ.hom.app ((pullbackTensorCalculus l E W).systemClosed.tensor.obj (M, N), P) ≫
      (pullbackTensorCalculus l L W).systemClosed.tensor.map
        (Prod.mkHom (σ.hom.app (M, N)) (𝟙 _)) ≫
      ((pullbackTensorCalculus l L W).systemClosed.monoidal.associator
        (H.obj M) (H.obj N) (H.obj P)).hom := by
  intro H σ
  let : MonoidalCategory (coefficientSequenceDerived l E W) :=
    (pullbackTensorCalculus l E W).systemClosed.monoidal
  let : MonoidalCategory (coefficientSequenceDerived l L W) :=
    (pullbackTensorCalculus l L W).systemClosed.monoidal
  have res (X : coefficientSequenceDerived l E W) :
      ∃ P : ScalarExtensionTower.Complex l E W, ScalarExtensionTower.Good l E W P ∧
        Nonempty (DerivedCategory.Q.obj P ≅ X) := by
    let q := DerivedCategory.Q (C := coefficientSequenceModules l E W)
    obtain ⟨P, f, hP, hflat, hf, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := coefficientSequenceCommRingSheaf l E W) (q.objPreimage X)
    have : QuasiIso f := hf
    refine ⟨P, ⟨hP, fun n ↦ ?_⟩, ⟨asIso (q.map f) ≪≫ q.objObjPreimageIso X⟩⟩
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso
        (coefficientSequenceCommRingSheaf l E W) (P.X n)).symm (hflat n)
  have hab : assocLeftPath H σ = assocRightPath H σ :=
    tripleNatTrans_ext_resolving DerivedCategory.Q (ScalarExtensionTower.Good l E W) res
      (assocLeftPath H σ) (assocRightPath H σ)
      (fun A B C hA hB hC ↦ scalarAssoc_representatives l E L ι W A B C hA hB hC)
  exact NatTrans.congr_app hab (M, N, P)


/-- Scalar extension of coherent systems sends the coefficient-ring unit to the
coefficient-ring unit.

Source: Stacks 03EL; extension of scalars of a free module of rank one.
(blueprint: lem-pur-system-scalar-tensor-braiding).

Proof: the coherent unit is the degree-zero single complex on the structure sheaf; it is
flat-term K-flat, so the scalar model computes its derived extension by the underived one, and
extension of scalars of the structure sheaf is the structure sheaf. -/
theorem systemScalarTensorUnitObject :
    Nonempty ((integralComparisonDerivedSequenceScalar l E L ι W).obj
        (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit ≅
      (pullbackTensorCalculus l L W).systemClosed.monoidal.tensorUnit) := by
  obtain ⟨_, ⟨cE⟩⟩ := scalar_systemTensorCoherence l E W
  obtain ⟨_, ⟨cL⟩⟩ := scalar_systemTensorCoherence l L W
  let δ := integralComparisonSequenceScalarModel.{u, u} l E L ι W
  let J := coefficientSequenceTopology (ProEt.topology W)
  let RE := coefficientSequenceCommRingSheaf.{u, u} l E W
  let RL := coefficientSequenceCommRingSheaf.{u, u} l L W
  have hk := unit_kflat.{u + 1, u, u} J RE
  have hiso : IsIso (δ.ε.app (ringedTensorUnitComplex.{u + 1, u, u} J RE)) := δ.computes _ hk
  let φ : (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RE ⟶
      ((𝟭 _).sheafPushforwardContinuous RingCat.{u + 1} J J).obj
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RL) :=
    ⟨Functor.whiskerRight (integralComparisonSequenceScalarMap.{u, u} l E L ι W).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  let adj : δ.E ⊣ SheafOfModules.pushforward φ := ScalarExtensionTower.scalar_adj l E L ι W
  let : (SheafOfModules.pushforward φ).IsRightAdjoint := adj.isRightAdjoint
  let e₀ : δ.E.obj (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{u + 1}
      RingCat.{u + 1})).obj RE)) ≅
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RL) :=
    (adj.leftAdjointUniq (SheafOfModules.pullbackPushforwardAdjunction φ)).app _ ≪≫
      asIso (SheafOfModules.pullbackObjUnitToUnit φ)
  let c : (δ.E.mapHomologicalComplex (.up ℤ)).obj (ringedTensorUnitComplex.{u + 1, u, u} J RE) ≅
      ringedTensorUnitComplex.{u + 1, u, u} J RL :=
    (HomologicalComplex.singleMapHomologicalComplex δ.E (.up ℤ) 0).app _ ≪≫
      (HomologicalComplex.single _ (.up ℤ) 0).mapIso e₀
  exact ⟨(integralComparisonDerivedSequenceScalar l E L ι W).mapIso cE.unitIso ≪≫
    @asIso _ _ _ _ (δ.ε.app (ringedTensorUnitComplex.{u + 1, u, u} J RE)) hiso ≪≫
    DerivedCategory.Q.mapIso c ≪≫ cL.unitIso.symm⟩

universe a b c d in
private theorem scalarAssociativity_from_tensorHom
    {C : Type a} [Category.{b} C] [MonoidalCategory C]
    {D : Type c} [Category.{d} D] [MonoidalCategory D]
    (F : C ⥤ D) (μ : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    (h : ∀ A B M : C,
      F.map (α_ A B M).hom ≫ (μ.app (A, B ⊗ M)).hom ≫
          (𝟙 (F.obj A) ⊗ₘ (μ.app (B, M)).hom) =
        (μ.app (A ⊗ B, M)).hom ≫ ((μ.app (A, B)).hom ⊗ₘ 𝟙 (F.obj M)) ≫
          (α_ (F.obj A) (F.obj B) (F.obj M)).hom) (A B M : C) :
    F.map (α_ A B M).hom ≫ (μ.app (A, B ⊗ M)).hom ≫
        F.obj A ◁ (μ.app (B, M)).hom =
      (μ.app (A ⊗ B, M)).hom ≫ (μ.app (A, B)).hom ▷ F.obj M ≫
        (α_ (F.obj A) (F.obj B) (F.obj M)).hom := by
  have h' := h A B M
  dsimp only [Functor.comp_obj, tensor_obj, Functor.prod_obj] at h' ⊢
  simpa only [MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_id] using h'

/-- Both unit equations for the normalized whole-system scalar tensorator.

Source: Stacks 03EL and 07A4.
(blueprint: lem-pur-system-scalar-tensor-braiding).

Proof: the associativity equation and any identification of the scalar extension of the unit
are combined by the monoidal unit extraction lemma. -/
theorem systemScalarTensorUnit :
    let H := integralComparisonDerivedSequenceScalar l E L ι W
    let σ := ScalarExtensionTower.derivedSigma l E L ι W
      (pullbackTensorCalculus l E W) (pullbackTensorCalculus l L W)
    ∃ ε : H.obj (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit ≅
      (pullbackTensorCalculus l L W).systemClosed.monoidal.tensorUnit,
      ∀ M : coefficientSequenceDerived l E W,
        (σ.hom.app ((pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit, M) ≫
          (pullbackTensorCalculus l L W).systemClosed.tensor.map
            (Prod.mkHom ε.hom (𝟙 _)) ≫
          ((pullbackTensorCalculus l L W).systemClosed.monoidal.leftUnitor (H.obj M)).hom =
        H.map ((pullbackTensorCalculus l E W).systemClosed.monoidal.leftUnitor M).hom) ∧
        (σ.hom.app (M, (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit) ≫
          (pullbackTensorCalculus l L W).systemClosed.tensor.map
            (Prod.mkHom (𝟙 _) ε.hom) ≫
          ((pullbackTensorCalculus l L W).systemClosed.monoidal.rightUnitor (H.obj M)).hom =
        H.map ((pullbackTensorCalculus l E W).systemClosed.monoidal.rightUnitor M).hom) := by
  let : MonoidalCategory (coefficientSequenceDerived l E W) :=
    (pullbackTensorCalculus l E W).systemClosed.monoidal
  let : MonoidalCategory (coefficientSequenceDerived l L W) :=
    (pullbackTensorCalculus l L W).systemClosed.monoidal
  let H := integralComparisonDerivedSequenceScalar l E L ι W
  let σ := ScalarExtensionTower.derivedSigma l E L ι W
    (pullbackTensorCalculus l E W) (pullbackTensorCalculus l L W)
  obtain ⟨e⟩ := systemScalarTensorUnitObject l E L ι W
  have hAssoc := scalarAssociativity_from_tensorHom H σ
    (systemScalarTensorAssociativity l E L ι W)
  obtain ⟨ε, hL, hR⟩ := unit_from_tensor H σ e hAssoc
  exact ⟨ε, fun M ↦ ⟨hL M, hR M⟩⟩

end WeilConjectures
