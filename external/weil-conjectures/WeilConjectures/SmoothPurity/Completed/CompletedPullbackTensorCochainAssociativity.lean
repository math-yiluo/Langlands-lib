/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
import all WeilConjectures.CategoryTheory.Ringed.Tensor.RingedTensorConstraintCompletion
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence

/-! # Associativity of the normalized sequence pullback on cochains

Source: Stacks 07A4 and the total tensor construction, Tag 06YN.
(blueprint: lem-pur-completed-pullback-tensor-cochain-associativity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
  AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures
attribute [local irreducible] pullbackTensorSequenceInverse pullbackTensorSequenceAdjunction
  pullbackTensorSequenceCochain pullbackTensorSequenceRing Functor.leftAdjoint
  SheafOfModules.monoidalCategory HasDerivedCategory.standard
  HomologicalComplex₂.total CategoryTheory.Functor.mapBifunctorHomologicalComplex
attribute [local implicit_reducible] pullbackTensorSequenceDirect 

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Paste a cochain square through an adjunction unit.
Source: naturality of the adjunction unit
(blueprint: lem-pur-completed-pullback-tensor-cochain-associativity). -/
private theorem adjunction_comparison_paste {B D : Type*} [Category B] [Category D]
    {L : B ⥤ D} {R : D ⥤ B} (adj : L ⊣ R)
    {P Q : B} {T V T' V' : D} (a : P ⟶ Q)
    (b : L.obj Q ⟶ T) (c : T ⟶ V)
    (b' : L.obj P ⟶ T') (c' : T' ⟶ V') (d : V' ⟶ V)
    (h : a ≫ adj.unit.app Q ≫ R.map b ≫ R.map c =
      adj.unit.app P ≫ R.map b' ≫ R.map c' ≫ R.map d) :
    L.map a ≫ b ≫ c = b' ≫ c' ≫ d := by
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Functor.map_comp]
  have hu := adj.unit.naturality a
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  rw [← Category.assoc, ← hu]
  simpa only [Category.assoc] using h

/-- Pasting the six pure-section equations requires only function congruence.
Source: the pure-tensor calculation of Stacks 07A4
(blueprint: lem-pur-completed-pullback-tensor-cochain-associativity). -/
private theorem associativitySectionSquare
    {A B C D E F G H : Type*}
    (σ : A → B) (ηB : B → C) (κB : C → D) (tB : D → H)
    (ηA : A → E) (κA : E → F) (tA : F → G) (τ : G → H)
    (x : A) (b : B) (d : D) (h : H) (f : F) (g : G)
    (hσ : σ x = b) (hκB : κB (ηB b) = d) (htB : tB d = h)
    (hκA : κA (ηA x) = f) (htA : tA f = g) (hτ : τ g = h) :
    tB (κB (ηB (σ x))) = τ (tA (κA (ηA x))) := by
  rw [hσ, hκB, htB, hκA, htA, hτ]

/-- The normalized sequence pullback commutes with cochain reassociation.
Source: Stacks 07A4, with the unsigned reassociation of Tag 06YN.
(blueprint: lem-pur-completed-pullback-tensor-cochain-associativity).

Proof: transpose the two chain maps by the inverse-image adjunction. Naturality
of its unit moves the source associator before the unit. Detect equality on each
triple total summand and then on local pure triples, using tensor sheafification.
The specified source associator rebrackets the triple without a sign. Apply the normalized
binary comparison twice on each side, and its naturality on tensor generators.
Both sections are x, y, z transported by the three adjunction units, with the
right parenthesization. The specified target associator gives this same section.
This argument uses neither K-flatness nor a derived associator. -/
theorem completedPullbackTensor_cochain_associativity {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q N : CochainComplex (coefficientSequenceModules l E Y) ℤ) :
    let JY := coefficientSequenceTopology (ProEt.topology Y)
    let JX := coefficientSequenceTopology (ProEt.topology X)
    let RY := coefficientSequenceCommRingSheaf l E Y
    let RX := coefficientSequenceCommRingSheaf l E X
    let V := (pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)
    let TY := coefficientTotalTensor.{u, u + 1, u} JY RY
    let T := coefficientTotalTensor.{u, u + 1, u} JX RX
    let κ := pullbackTensorSequenceCochain l E f
    ∀ (aY : TY.obj (TY.obj (P, Q), N) ≅ TY.obj (P, TY.obj (Q, N)))
      (aX : T.obj (T.obj (V.obj P, V.obj Q), V.obj N) ≅
        T.obj (V.obj P, T.obj (V.obj Q, V.obj N))),
    (∀ (p q r pq qr k : ℤ) (hpq : p + q = pq) (hqr : q + r = qr)
      (hn : pq + r = k) (hn' : p + qr = k) (U : (ℕ × Y.ProEt)ᵒᵖ)
      (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) (z : (N.X r).val.obj U),
      (aY.hom.f k).val.app U
        (coefficientTensorGenerator.{u, u + 1, u} JY RY (TY.obj (P, Q)) N pq r k hn U
          (coefficientTensorGenerator.{u, u + 1, u} JY RY P Q p q pq hpq U x y) z) =
      coefficientTensorGenerator.{u, u + 1, u} JY RY P (TY.obj (Q, N)) p qr k hn' U x
        (coefficientTensorGenerator.{u, u + 1, u} JY RY Q N q r qr hqr U y z)) →
    (∀ (p q r pq qr k : ℤ) (hpq : p + q = pq) (hqr : q + r = qr)
      (hn : pq + r = k) (hn' : p + qr = k) (U : (ℕ × X.ProEt)ᵒᵖ)
      (x : ((V.obj P).X p).val.obj U) (y : ((V.obj Q).X q).val.obj U)
      (z : ((V.obj N).X r).val.obj U),
      (aX.hom.f k).val.app U
        (coefficientTensorGenerator.{u, u + 1, u} JX RX
          (T.obj (V.obj P, V.obj Q)) (V.obj N) pq r k hn U
          (coefficientTensorGenerator.{u, u + 1, u} JX RX
            (V.obj P) (V.obj Q) p q pq hpq U x y) z) =
      coefficientTensorGenerator.{u, u + 1, u} JX RX
        (V.obj P) (T.obj (V.obj Q, V.obj N)) p qr k hn' U x
        (coefficientTensorGenerator.{u, u + 1, u} JX RX
          (V.obj Q) (V.obj N) q r qr hqr U y z)) →
    V.map aY.hom ≫ κ.hom.app (P, TY.obj (Q, N)) ≫
        T.map (Prod.mkHom (𝟙 (V.obj P)) (κ.hom.app (Q, N))) =
      κ.hom.app (TY.obj (P, Q), N) ≫
        T.map (Prod.mkHom (κ.hom.app (P, Q)) (𝟙 (V.obj N))) ≫ aX.hom := by
  let RY := coefficientSequenceCommRingSheaf l E Y
  let RX := coefficientSequenceCommRingSheaf l E X
  let JY := coefficientSequenceTopology (ProEt.topology Y)
  let JX := coefficientSequenceTopology (ProEt.topology X)
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{u + 1, u, u + 1} RY
  let := SheafOfModules.monoidalCategory RY
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{u + 1, u, u + 1} RX
  let := SheafOfModules.monoidalCategory RX
  let L := pullbackTensorSequenceInverse l E f
  let adj := pullbackTensorSequenceAdjunction l E f
  let V := L.mapHomologicalComplex (.up ℤ)
  let κ := pullbackTensorSequenceCochain l E f
  let TY := coefficientTotalTensor.{u, u + 1, u} JY RY
  let T := coefficientTotalTensor.{u, u + 1, u} JX RX
  dsimp only
  intro aY aX haY haX
  let : (pullbackTensorSequenceDirect l E f).Additive :=
    { map_add := by intros; rfl }
  have hκ := (pullbackTensorSequenceCochain_existsUnique l E f).exists.choose_spec
  apply adjunction_comparison_paste (adj.mapHomologicalComplex (.up ℤ))
  apply CategoryTheory.tensorGenerator_ext₃.{u + 1, u, u} JY RY P Q N
  intro p q r pq k hpq hn U x y z
  have hqr : q + r = q + r := rfl
  have hn' : p + (q + r) = k := by omega
  change ((T.map (Prod.mkHom (𝟙 (V.obj P)) (κ.hom.app (Q, N)))).f k).val.app
      (op ((pullbackTensorSequenceBase f).obj U.unop))
      (((κ.hom.app (P, TY.obj (Q, N))).f k).val.app
        (op ((pullbackTensorSequenceBase f).obj U.unop))
        ((adj.unit.app _).val.app U
          ((aY.hom.f k).val.app U
            (coefficientTensorGenerator.{u, u + 1, u} JY RY (TY.obj (P, Q)) N pq r k hn U
              (coefficientTensorGenerator.{u, u + 1, u} JY RY P Q p q pq hpq U x y) z)))) =
    (aX.hom.f k).val.app
      (op ((pullbackTensorSequenceBase f).obj U.unop))
      (((T.map (Prod.mkHom (κ.hom.app (P, Q)) (𝟙 (V.obj N)))).f k).val.app
        (op ((pullbackTensorSequenceBase f).obj U.unop))
        (((κ.hom.app (TY.obj (P, Q), N)).f k).val.app
          (op ((pullbackTensorSequenceBase f).obj U.unop))
          ((adj.unit.app _).val.app U
            (coefficientTensorGenerator.{u, u + 1, u} JY RY (TY.obj (P, Q)) N pq r k hn U
              (coefficientTensorGenerator.{u, u + 1, u} JY RY P Q p q pq hpq U x y) z))))
  let U' := op ((pullbackTensorSequenceBase f).obj U.unop)
  let xp := (adj.unit.app (P.X p)).val.app U x
  let yq := (adj.unit.app (Q.X q)).val.app U y
  let zr := (adj.unit.app (N.X r)).val.app U z
  let gPQ := coefficientTensorGenerator.{u, u + 1, u} JY RY P Q p q pq hpq U x y
  let gQN := coefficientTensorGenerator.{u, u + 1, u} JY RY Q N q r (q + r) hqr U y z
  let gY' := coefficientTensorGenerator.{u, u + 1, u} JY RY P (TY.obj (Q, N))
    p (q + r) k hn' U x gQN
  let gR := coefficientTensorGenerator.{u, u + 1, u} JX RX (V.obj P) (V.obj (TY.obj (Q, N)))
    p (q + r) k hn' U' xp ((adj.unit.app ((TY.obj (Q, N)).X (q + r))).val.app U gQN)
  let gL := coefficientTensorGenerator.{u, u + 1, u} JX RX (V.obj (TY.obj (P, Q))) (V.obj N)
    pq r k hn U' ((adj.unit.app ((TY.obj (P, Q)).X pq)).val.app U gPQ) zr
  let gPQ' := coefficientTensorGenerator.{u, u + 1, u} JX RX
    (V.obj P) (V.obj Q) p q pq hpq U' xp yq
  let gQN' := coefficientTensorGenerator.{u, u + 1, u} JX RX
    (V.obj Q) (V.obj N) q r (q + r) hqr U' yq zr
  let gL' := coefficientTensorGenerator.{u, u + 1, u} JX RX
    (T.obj (V.obj P, V.obj Q)) (V.obj N) pq r k hn U' gPQ' zr
  let gR' := coefficientTensorGenerator.{u, u + 1, u} JX RX
    (V.obj P) (T.obj (V.obj Q, V.obj N)) p (q + r) k hn' U' xp gQN'
  have hκ' : ∀ A B p q k h U x y,
      ((κ.hom.app (A, B)).f k).val.app
          (op ((pullbackTensorSequenceBase f).obj (unop U)))
        ((adj.unit.app _).val.app U
          (coefficientTensorGenerator.{u, u + 1, u} JY RY A B p q k h U x y)) =
      coefficientTensorGenerator.{u, u + 1, u} JX RX (V.obj A) (V.obj B) p q k h
        (op ((pullbackTensorSequenceBase f).obj (unop U)))
        ((adj.unit.app (A.X p)).val.app U x)
        ((adj.unit.app (B.X q)).val.app U y) := by
    intro A B p q k h U x y
    dsimp only [κ, adj]
    unfold pullbackTensorSequenceCochain
    exact hκ A B p q k h U.unop x y
  refine associativitySectionSquare
    ((aY.hom.f k).val.app U)
    ((adj.unit.app ((TY.obj (P, TY.obj (Q, N))).X k)).val.app U)
    (((κ.hom.app (P, TY.obj (Q, N))).f k).val.app U')
    (((T.map (Prod.mkHom (𝟙 (V.obj P)) (κ.hom.app (Q, N)))).f k).val.app U')
    ((adj.unit.app ((TY.obj (TY.obj (P, Q), N)).X k)).val.app U)
    (((κ.hom.app (TY.obj (P, Q), N)).f k).val.app U')
    (((T.map (Prod.mkHom (κ.hom.app (P, Q)) (𝟙 (V.obj N)))).f k).val.app U')
    ((aX.hom.f k).val.app U')
    _ gY' gR gR' gL gL' ?_ ?_ ?_ ?_ ?_ ?_
  · exact haY p q r pq (q + r) k hpq hqr hn hn' U x y z
  · exact hκ' P (TY.obj (Q, N)) p (q + r) k hn' U x gQN
  · have hm := CategoryTheory.ScalarHomTensor.tensor_generator_map.{u + 1, u, u}
      (𝟙 (V.obj P)) (κ.hom.app (Q, N)) p (q + r) k hn' U' xp
      ((adj.unit.app ((TY.obj (Q, N)).X (q + r))).val.app U gQN)
    simp only [HomologicalComplex.id_f, SheafOfModules.id_val,
      PresheafOfModules.id_app] at hm
    exact hm.trans (congrArg (fun w ↦ coefficientTensorGenerator.{u, u + 1, u}
      JX RX (V.obj P) (T.obj (V.obj Q, V.obj N)) p (q + r) k hn' U' xp w)
      (hκ' Q N q r (q + r) hqr U y z))
  · exact hκ' (TY.obj (P, Q)) N pq r k hn U gPQ z
  · have hm := CategoryTheory.ScalarHomTensor.tensor_generator_map.{u + 1, u, u}
      (κ.hom.app (P, Q)) (𝟙 (V.obj N)) pq r k hn U'
      ((adj.unit.app ((TY.obj (P, Q)).X pq)).val.app U gPQ) zr
    simp only [HomologicalComplex.id_f, SheafOfModules.id_val,
      PresheafOfModules.id_app] at hm
    exact hm.trans (congrArg (fun w ↦ coefficientTensorGenerator.{u, u + 1, u}
      JX RX (T.obj (V.obj P, V.obj Q)) (V.obj N) pq r k hn U' w zr)
      (hκ' P Q p q pq hpq U x y))
  · exact haX p q r pq (q + r) k hpq hqr hn hn' U' xp yq zr

end WeilConjectures
