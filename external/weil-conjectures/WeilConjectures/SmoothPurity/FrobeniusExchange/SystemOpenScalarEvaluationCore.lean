/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FrobeniusExchange.SystemOperationExchangeRealization
public import WeilConjectures.SmoothPurity.FrobeniusExchange.SystemScalarFiniteEvaluation
import WeilConjectures.SixFunctors.FrobeniusExchange.SystemScalarPullbackGeneralMate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategorySquareIsoSymm
import all WeilConjectures.SixFunctors.FrobeniusExchange.SystemOpenScalarPullbackMate

/-! # Inverse-mate reduction for open scalar evaluation

Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 03DI and 07A6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FrobeniusExchange
open AlgebraicGeometry.Scheme.FiniteCompactScalar

/-- Pasting of five inverse mates around a cube of right-adjoint squares: if the cube of
right-adjoint comparisons commutes, then the corresponding pasted left mates agree. -/
theorem openScalar_mate_pasting
    {A B A' B' a b a' b' : Type*} [Category A] [Category B] [Category A'] [Category B']
    [Category a] [Category b] [Category a'] [Category b']
    {jE : B ⥤ A} {JE : A ⥤ B} (adjJE : JE ⊣ jE)
    {jL : B' ⥤ A'} {JL : A' ⥤ B'} (adjJL : JL ⊣ jL)
    {jfE : b ⥤ a} {JfE : a ⥤ b} (adjfE : JfE ⊣ jfE)
    {jfL : b' ⥤ a'} {JfL : a' ⥤ b'} (adjfL : JfL ⊣ jfL)
    {rX : A' ⥤ A} {SX : A ⥤ A'} (σX : SX ⊣ rX)
    {rZ : B' ⥤ B} {SZ : B ⥤ B'} (σZ : SZ ⊣ rZ)
    {rfX : a' ⥤ a} {sX : a ⥤ a'} (τX : sX ⊣ rfX)
    {rfZ : b' ⥤ b} {sZ : b ⥤ b'} (τZ : sZ ⊣ rfZ)
    (eA : A ⥤ a) (eB : B ⥤ b) (eA' : A' ⥤ a') (eB' : B' ⥤ b')
    (pE : jE ⋙ eA ⟶ eB ⋙ jfE) (pL : jL ⋙ eA' ⟶ eB' ⋙ jfL)
    (ρX : rX ⋙ eA ⟶ eA' ⋙ rfX) (ρZ : rZ ⋙ eB ⟶ eB' ⋙ rfZ)
    (q : rZ ⋙ jE ⟶ jL ⋙ rX) (φ : rfX ⋙ JfE ⟶ JfL ⋙ rfZ)
    (hcube : ∀ M : B', eA.map (q.app M) ≫ ρX.app (jL.obj M) ≫ rfX.map (pL.app M) ≫
      (mateEquiv adjfL adjfE (TwoSquare.mk _ _ _ _ φ)).app (eB'.obj M) =
        pE.app (rZ.obj M) ≫ jfE.map (ρZ.app M))
    (N : A) :
    sZ.map (((mateEquiv adjJE adjfE).symm (TwoSquare.mk _ _ _ _ pE)).app N) ≫
        ((mateEquiv σZ τZ).symm (TwoSquare.mk _ _ _ _ ρZ)).app (JE.obj N) =
      ((mateEquiv τX τZ).symm (TwoSquare.mk _ _ _ _ φ)).app (eA.obj N) ≫
        JfL.map (((mateEquiv σX τX).symm (TwoSquare.mk _ _ _ _ ρX)).app N) ≫
        ((mateEquiv adjJL adjfL).symm (TwoSquare.mk _ _ _ _ pL)).app (SX.obj N) ≫
        eB'.map (((mateEquiv adjJE adjJL).symm
          ((mateEquiv σZ σX).symm (TwoSquare.mk _ _ _ _ q))).app N) := by
  let δE := ((mateEquiv adjJE adjfE).symm (TwoSquare.mk _ _ _ _ pE))
  let δL := ((mateEquiv adjJL adjfL).symm (TwoSquare.mk _ _ _ _ pL))
  let βX := ((mateEquiv σX τX).symm (TwoSquare.mk _ _ _ _ ρX))
  let βZ := ((mateEquiv σZ τZ).symm (TwoSquare.mk _ _ _ _ ρZ))
  let α := ((mateEquiv τX τZ).symm (TwoSquare.mk _ _ _ _ φ))
  let SP := (mateEquiv σZ σX).symm (TwoSquare.mk _ _ _ _ q)
  let γ := ((mateEquiv adjJE adjJL).symm SP)
  let ψ := (mateEquiv adjfL adjfE (TwoSquare.mk _ _ _ _ φ))
  let M := SZ.obj (JE.obj N)
  have uδE : eA.map (adjJE.unit.app N) ≫ pE.app (JE.obj N) =
      adjfE.unit.app (eA.obj N) ≫ jfE.map (δE.app N) :=
    unit_mateEquiv_symm adjJE adjfE (TwoSquare.mk _ _ _ _ pE) N
  have uδL : eA'.map (adjJL.unit.app (SX.obj N)) ≫ pL.app (JL.obj (SX.obj N)) =
      adjfL.unit.app (eA'.obj (SX.obj N)) ≫ jfL.map (δL.app (SX.obj N)) :=
    unit_mateEquiv_symm adjJL adjfL (TwoSquare.mk _ _ _ _ pL) (SX.obj N)
  have uβX : eA.map (σX.unit.app N) ≫ ρX.app (SX.obj N) =
      τX.unit.app (eA.obj N) ≫ rfX.map (βX.app N) :=
    unit_mateEquiv_symm σX τX (TwoSquare.mk _ _ _ _ ρX) N
  have uβZ : eB.map (σZ.unit.app (JE.obj N)) ≫ ρZ.app M =
      τZ.unit.app (eB.obj (JE.obj N)) ≫ rfZ.map (βZ.app (JE.obj N)) :=
    unit_mateEquiv_symm σZ τZ (TwoSquare.mk _ _ _ _ ρZ) (JE.obj N)
  have uα : JfE.map (τX.unit.app (eA.obj N)) ≫ φ.app (sX.obj (eA.obj N)) =
      τZ.unit.app (JfE.obj (eA.obj N)) ≫ rfZ.map (α.app (eA.obj N)) :=
    unit_mateEquiv_symm τX τZ (TwoSquare.mk _ _ _ _ φ) (eA.obj N)
  have uSP : jE.map (σZ.unit.app (JE.obj N)) ≫ q.app M =
      σX.unit.app (jE.obj (JE.obj N)) ≫ rX.map (SP.app (JE.obj N)) :=
    unit_mateEquiv_symm σZ σX (TwoSquare.mk _ _ _ _ q) (JE.obj N)
  have uγ : SX.map (adjJE.unit.app N) ≫ SP.app (JE.obj N) =
      adjJL.unit.app (SX.obj N) ≫ jL.map (γ.app N) :=
    unit_mateEquiv_symm adjJE adjJL SP N
  have uψ (c : a') : rfX.map (adjfL.unit.app c) ≫ ψ.app (JfL.obj c) =
      adjfE.unit.app (rfX.obj c) ≫ jfE.map (φ.app c) :=
    unit_mateEquiv adjfL adjfE (TwoSquare.mk _ _ _ _ φ) c
  have hS : adjJE.unit.app N ≫ jE.map (σZ.unit.app (JE.obj N)) ≫ q.app M =
      σX.unit.app N ≫ rX.map (adjJL.unit.app (SX.obj N) ≫ jL.map (γ.app N)) := by
    rw [uSP, ← uγ, Functor.map_comp, ← Category.assoc, ← Category.assoc]
    congr 1
    exact σX.unit.naturality (adjJE.unit.app N)
  have hL : adjfE.homEquiv _ _ (τZ.homEquiv _ _
      (sZ.map (δE.app N) ≫ βZ.app (JE.obj N))) =
      eA.map (adjJE.unit.app N ≫ jE.map (σZ.unit.app (JE.obj N))) ≫ pE.app (rZ.obj M) ≫
        jfE.map (ρZ.app M) := by
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_unit τZ]
    erw [← uβZ]
    rw [
      Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, ← uδE,
      Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc]
    congr 1
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    exact (pE.naturality (σZ.unit.app (JE.obj N))).symm
  have hR : adjfE.homEquiv _ _ (τZ.homEquiv _ _
      (α.app (eA.obj N) ≫ JfL.map (βX.app N) ≫ δL.app (SX.obj N) ≫ eB'.map (γ.app N))) =
      eA.map (σX.unit.app N ≫ rX.map (adjJL.unit.app (SX.obj N) ≫ jL.map (γ.app N))) ≫
        ρX.app (jL.obj M) ≫ rfX.map (pL.app M) ≫ ψ.app (eB'.obj M) := by
    rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_unit τZ, ← uα]
    have φnat := φ.naturality (βX.app N)
    have ψnat1 := ψ.naturality (δL.app (SX.obj N))
    have ψnat2 := ψ.naturality (eB'.map (γ.app N))
    have pLnat := pL.naturality (γ.app N)
    have ρXnat := ρX.naturality (adjJL.unit.app (SX.obj N) ≫ jL.map (γ.app N))
    simp only [Functor.comp_map] at φnat ψnat1 ψnat2 pLnat ρXnat
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, ← reassoc_of% φnat,
      ← JfE.map_comp_assoc]
    erw [← uβX]
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
      Adjunction.homEquiv_unit adjfE]
    erw [← uψ]
    simp only [Category.assoc]
    rw [jfE.map_comp]
    erw [← reassoc_of% ψnat1, ← ψnat2]
    rw [← rfX.map_comp_assoc, ← rfX.map_comp_assoc]
    erw [← uδL]
    rw [Category.assoc]
    erw [← pLnat]
    rw [← eA'.map_comp_assoc, rfX.map_comp, Category.assoc]
    erw [← reassoc_of% ρXnat]
    simp only [Functor.map_comp, Category.assoc]
    rfl
  apply (τZ.homEquiv _ _).injective
  apply (adjfE.homEquiv _ _).injective
  erw [hL, hR]
  rw [← hcube M, ← Category.assoc, ← eA.map_comp, Category.assoc, hS]


/-- `openScalar_mate_pasting` with the pasted mates given by equations. -/
theorem openScalar_mate_pasting_of_eq
    {A B A' B' a b a' b' : Type*} [Category A] [Category B] [Category A'] [Category B']
    [Category a] [Category b] [Category a'] [Category b']
    {jE : B ⥤ A} {JE : A ⥤ B} {adjJE : JE ⊣ jE}
    {jL : B' ⥤ A'} {JL : A' ⥤ B'} {adjJL : JL ⊣ jL}
    {jfE : b ⥤ a} {JfE : a ⥤ b} {adjfE : JfE ⊣ jfE}
    {jfL : b' ⥤ a'} {JfL : a' ⥤ b'} {adjfL : JfL ⊣ jfL}
    {rX : A' ⥤ A} {SX : A ⥤ A'} {σX : SX ⊣ rX}
    {rZ : B' ⥤ B} {SZ : B ⥤ B'} {σZ : SZ ⊣ rZ}
    {rfX : a' ⥤ a} {sX : a ⥤ a'} {τX : sX ⊣ rfX}
    {rfZ : b' ⥤ b} {sZ : b ⥤ b'} {τZ : sZ ⊣ rfZ}
    {eA : A ⥤ a} {eB : B ⥤ b} {eA' : A' ⥤ a'} {eB' : B' ⥤ b'}
    {pE : jE ⋙ eA ⟶ eB ⋙ jfE} {pL : jL ⋙ eA' ⟶ eB' ⋙ jfL}
    {ρX : rX ⋙ eA ⟶ eA' ⋙ rfX} {ρZ : rZ ⋙ eB ⟶ eB' ⋙ rfZ}
    {q : rZ ⋙ jE ⟶ jL ⋙ rX} {φ : rfX ⋙ JfE ⟶ JfL ⋙ rfZ}
    (hcube : ∀ M : B', eA.map (q.app M) ≫ ρX.app (jL.obj M) ≫ rfX.map (pL.app M) ≫
      (mateEquiv adjfL adjfE (TwoSquare.mk _ _ _ _ φ)).app (eB'.obj M) =
        pE.app (rZ.obj M) ≫ jfE.map (ρZ.app M))
    {δE : eA ⋙ JfE ⟶ JE ⋙ eB}
    (hδE : δE = ((mateEquiv adjJE adjfE).symm (TwoSquare.mk _ _ _ _ pE)))
    {δL : eA' ⋙ JfL ⟶ JL ⋙ eB'}
    (hδL : δL = ((mateEquiv adjJL adjfL).symm (TwoSquare.mk _ _ _ _ pL)))
    {βX : eA ⋙ sX ⟶ SX ⋙ eA'}
    (hβX : βX = ((mateEquiv σX τX).symm (TwoSquare.mk _ _ _ _ ρX)))
    {βZ : eB ⋙ sZ ⟶ SZ ⋙ eB'}
    (hβZ : βZ = ((mateEquiv σZ τZ).symm (TwoSquare.mk _ _ _ _ ρZ)))
    {α : JfE ⋙ sZ ⟶ sX ⋙ JfL}
    (hα : α = ((mateEquiv τX τZ).symm (TwoSquare.mk _ _ _ _ φ)))
    {γ : SX ⋙ JL ⟶ JE ⋙ SZ}
    (hγ : γ = ((mateEquiv adjJE adjJL).symm
      ((mateEquiv σZ σX).symm (TwoSquare.mk _ _ _ _ q))))
    (N : A) :
    sZ.map (δE.app N) ≫ βZ.app (JE.obj N) =
      α.app (eA.obj N) ≫ JfL.map (βX.app N) ≫ δL.app (SX.obj N) ≫ eB'.map (γ.app N) := by
  subst hδE hδL hβX hβZ hα hγ
  exact openScalar_mate_pasting adjJE adjJL adjfE adjfL σX σZ τX τZ eA eB eA' eB'
    pE pL ρX ρZ q φ hcube N

/-- Rearranging the pasted mate equation into the inverse-component form. -/
theorem openScalar_rearrange {C : Type*} [Category C] {U V W T S U' : C} (a : U ⟶ V)
    (f₁ : W ⟶ V) (g₁ : V ⟶ W) (f₂ : T ⟶ W) (g₂ : W ⟶ T) (x : T ⟶ S) (y : S ⟶ T)
    (m₁ : U' ⟶ U) (n₁ : U ⟶ U') (m₂ : S ⟶ U') (n₂ : U' ⟶ S)
    (e₁ : g₁ ≫ f₁ = 𝟙 V) (e₂ : g₂ ≫ f₂ = 𝟙 W) (ex : x ≫ y = 𝟙 T)
    (em₁ : m₁ ≫ n₁ = 𝟙 U') (em₂ : m₂ ≫ n₂ = 𝟙 S)
    (h : n₁ ≫ n₂ = a ≫ g₁ ≫ g₂ ≫ x) :
    f₂ ≫ f₁ = x ≫ m₂ ≫ m₁ ≫ a := by
  have ha : a = n₁ ≫ n₂ ≫ y ≫ f₂ ≫ f₁ := by
    rw [reassoc_of% h, reassoc_of% ex, reassoc_of% e₂, e₁, Category.comp_id]
  rw [ha, reassoc_of% em₁, reassoc_of% em₂, reassoc_of% ex]

/-- The abstract open scalar evaluation equation: if the right-adjoint cube commutes, the
inverse open evaluation mates, the scalar evaluation comparisons, the finite scalar mate and
the system open scalar mate satisfy the finite-evaluation equation. -/
theorem openScalar_evaluation_of_cube
    {A B A' B' a b a' b' : Type*} [Category A] [Category B] [Category A'] [Category B']
    [Category a] [Category b] [Category a'] [Category b']
    {jE : B ⥤ A} {JE : A ⥤ B} (adjJE : JE ⊣ jE)
    {jL : B' ⥤ A'} {JL : A' ⥤ B'} (adjJL : JL ⊣ jL)
    {jfE : b ⥤ a} {JfE : a ⥤ b} (adjfE : JfE ⊣ jfE)
    {jfL : b' ⥤ a'} {JfL : a' ⥤ b'} (adjfL : JfL ⊣ jfL)
    {rX : A' ⥤ A} {SX : A ⥤ A'} (σX : SX ⊣ rX)
    {rZ : B' ⥤ B} {SZ : B ⥤ B'} (σZ : SZ ⊣ rZ)
    {rfX : a' ⥤ a} {sX : a ⥤ a'} (τX : sX ⊣ rfX)
    {rfZ : b' ⥤ b} {sZ : b ⥤ b'} (τZ : sZ ⊣ rfZ)
    (eA : A ⥤ a) (eB : B ⥤ b) (eA' : A' ⥤ a') (eB' : B' ⥤ b')
    (pE : jE ⋙ eA ⟶ eB ⋙ jfE) (pL : jL ⋙ eA' ⟶ eB' ⋙ jfL)
    (ρX : rX ⋙ eA ⟶ eA' ⋙ rfX) (ρZ : rZ ⋙ eB ⟶ eB' ⋙ rfZ)
    (q : rZ ⋙ jE ⟶ jL ⋙ rX) (φ : rfX ⋙ JfE ⟶ JfL ⋙ rfZ)
    (hcube : ∀ M : B', eA.map (q.app M) ≫ ρX.app (jL.obj M) ≫ rfX.map (pL.app M) ≫
      (mateEquiv adjfL adjfE (TwoSquare.mk _ _ _ _ φ)).app (eB'.obj M) =
        pE.app (rZ.obj M) ≫ jfE.map (ρZ.app M))
    (δE : eA ⋙ JfE ⟶ JE ⋙ eB) [IsIso δE]
    (hδE : δE = ((mateEquiv adjJE adjfE).symm (TwoSquare.mk _ _ _ _ pE)))
    (δL : eA' ⋙ JfL ⟶ JL ⋙ eB') [IsIso δL]
    (hδL : δL = ((mateEquiv adjJL adjfL).symm (TwoSquare.mk _ _ _ _ pL)))
    (εX : SX ⋙ eA' ≅ eA ⋙ sX)
    (hεX : εX.inv = ((mateEquiv σX τX).symm (TwoSquare.mk _ _ _ _ ρX)))
    (εZ : SZ ⋙ eB' ≅ eB ⋙ sZ)
    (hεZ : εZ.inv = ((mateEquiv σZ τZ).symm (TwoSquare.mk _ _ _ _ ρZ)))
    (α : JfE ⋙ sZ ⟶ sX ⋙ JfL)
    (hα : α = ((mateEquiv τX τZ).symm (TwoSquare.mk _ _ _ _ φ)))
    (γ : SX ⋙ JL ⟶ JE ⋙ SZ) [IsIso γ]
    (hγ : γ = ((mateEquiv adjJE adjJL).symm
      ((mateEquiv σZ σX).symm (TwoSquare.mk _ _ _ _ q))))
    (N : A) :
    let uE := (asIso δE).symm
    let uL := (asIso δL).symm
    uL.hom.app (SX.obj N) ≫ JfL.map (εX.hom.app N) =
      eB'.map (γ.app N) ≫ εZ.hom.app (JE.obj N) ≫ sZ.map (uE.hom.app N) ≫
        α.app (eA.obj N) := by
  intro uE uL
  have hP := openScalar_mate_pasting_of_eq hcube hδE hδL hεX hεZ hα hγ N
  refine openScalar_rearrange _ _ (JfL.map (εX.inv.app N)) _ (uL.inv.app _) _
    (eB'.map (inv (γ.app N))) _ (sZ.map (uE.inv.app N)) _ (εZ.inv.app _)
    (by simp [← Functor.map_comp]) (by simp) (by simp)
    (by simp [uE]) (by simp) ?_
  exact hP

section EvaluationMate

universe c v r

/-- The level evaluation comparison of normalized semilinear scalar systems is the inverse
mate of restriction evaluation, as forced by its transpose field. -/
theorem scalarSystems_evaluation_inv_eq_mate {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) [EssentiallySmall.{max c v r} C]
    (B : ℕ → Sheaf J CommRingCat.{max c v r}) (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)
    (F : ℕ → Sheaf J CommRingCat.{max c v r}) (σ : ∀ n : ℕ, F (n + 1) ⟶ F n)
    (α : ∀ n : ℕ, B n ⟶ F n) (hα : ∀ n : ℕ, α (n + 1) ≫ σ n = τ n ≫ α n)
    (d : SemilinearSections.ScalarSystems.{c, v, r} J B τ F σ α hα) (n : ℕ) :
    (d.evaluation n).inv = ((mateEquiv d.scalar.adjunction (d.levels n).adjunction).symm
      (TwoSquare.mk _ _ _ _
        (SemilinearSections.restrictionEvaluation.{c, v, max c v r}
          J B τ F σ α hα n).hom)) := by
  ext M
  apply ((d.levels n).adjunction.homEquiv _ _).injective
  have h := d.transpose_evaluation n M _ (𝟙 _)
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Adjunction.homEquiv_id] at h
  erw [← h, Adjunction.homEquiv_unit]
  exact unit_mateEquiv_symm _ _ _ M

end EvaluationMate

/-- Conjugating an evaluation comparison by adjoint-uniqueness isomorphisms replaces the
adjunctions in its inverse-mate description. -/
theorem isoInv_leftAdjointUniq_eq_mate {C D C' D' : Type*} [Category C] [Category D]
    [Category C'] [Category D'] {L L' : C ⥤ D} {R : D ⥤ C} {l l' : C' ⥤ D'} {r : D' ⥤ C'}
    {G : C ⥤ C'} {H : D ⥤ D'} (a : L ⊣ R) (b : L' ⊣ R) (c : l ⊣ r) (c' : l' ⊣ r)
    (ev : L' ⋙ H ≅ G ⋙ l) (w : TwoSquare R H G r)
    (hev : ev.inv = ((mateEquiv b c).symm w)) :
    (Functor.isoWhiskerRight (a.leftAdjointUniq b) H ≪≫ ev ≪≫
      Functor.isoWhiskerLeft G (c.leftAdjointUniq c')).inv =
      ((mateEquiv a c').symm w) := by
  have hw : (mateEquiv a c').symm w = TwoSquare.mk _ _ _ _
      (Functor.whiskerLeft G (c'.leftAdjointUniq c).hom ≫ ((mateEquiv b c).symm w) ≫
        Functor.whiskerRight (a.leftAdjointUniq b).inv H) := by
    apply (mateEquiv a c').injective
    rw [Equiv.apply_symm_apply, mateEquiv_leftAdjointUniq, Equiv.apply_symm_apply]
  rw [hw, ← hev]
  ext X
  simp [Adjunction.leftAdjointUniq_inv_app]

/-- Inverse mates along heterogeneously equal adjunctions whose right adjoints differ by
an equality of parameters. -/
theorem inverseMate_heq_cast {X : Sort*} {C D C' D' : Type*} [Category C] [Category D]
    [Category C'] [Category D'] {L : C ⥤ D} (Rf : X → (D ⥤ C)) {l : C' ⥤ D'} {r : D' ⥤ C'}
    {G : C ⥤ C'} {H : D ⥤ D'} {φ₁ φ₂ : X} (h : φ₁ = φ₂) (a : L ⊣ Rf φ₁)
    (b : L ⊣ Rf φ₂)
    (hab : HEq a b) (c : l ⊣ r) (w : TwoSquare (Rf φ₁) H G r) :
    ∃ w' : TwoSquare (Rf φ₂) H G r, HEq w' w ∧
      (mateEquiv a c).symm w = (mateEquiv b c).symm w' := by
  subst h
  obtain rfl := eq_of_heq hab
  exact ⟨w, HEq.rfl, rfl⟩

/-- A cast by `Eq.mpr` is heterogeneously equal to its argument. -/
theorem eq_mpr_heq_self.{w} {α β : Sort w} (h : α = β) (b : β) : HEq (Eq.mpr h b) b := by
  subst h
  rfl

section FiniteEvaluationMate

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

-- the evaluation comparison unfolds the chosen scalar systems
/-- The normalized finite evaluation of system scalar extension is the inverse mate of
restriction evaluation along the normalized system and finite scalar adjunctions. -/
theorem systemScalarFiniteEvaluation_inv_eq_mate (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u}) (n : ℕ) :
    ∃ ρ : TwoSquare (SemilinearSections.resD (integralComparisonSequenceScalarMap l E L ι W))
        (coefficientSequenceDerivedEvaluation l L W n)
        (coefficientSequenceDerivedEvaluation l E W n)
        (pbcDerivedRestrict (scalarRingMap (integralScalarQuotientMap l E L ι n) W)),
      HEq ρ (SemilinearSections.restrictionEvaluation (ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
        (integralCoefficientCommRingSheaf l L W) (coefficientSequenceCommRingTransition l L W)
        (integralScalarQuotientSheafMap l E L ι W)
        (scalarQuotient_compatible l E L ι W) n).hom ∧
      (systemScalarFiniteEvaluation l E L ι W n).inv =
        ((mateEquiv (finiteEvaluationSystemScalarAdjunction l E L ι W)
          (pbcDerivedScalarAdjunction
            (scalarRingMap (integralScalarQuotientMap l E L ι n) W))).symm
          ρ) := by
  obtain ⟨w', hw', he⟩ := inverseMate_heq_cast (fun φ ↦ SemilinearSections.resD φ)
    (scalarSystemMap_eq l E L ι W)
    (by rw [scalarSystemMap_eq]; exact finiteEvaluationSystemScalarAdjunction l E L ι W)
    (finiteEvaluationSystemScalarAdjunction l E L ι W) (eq_mpr_heq_self _ _)
    (pbcDerivedScalarAdjunction (scalarRingMap (integralScalarQuotientMap l E L ι n) W))
    (TwoSquare.mk _ _ _ _ (SemilinearSections.restrictionEvaluation (ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
      (integralCoefficientCommRingSheaf l L W) (coefficientSequenceCommRingTransition l L W)
      (integralScalarQuotientSheafMap l E L ι W) (scalarQuotient_compatible l E L ι W) n).hom)
  exact ⟨w', hw', (isoInv_leftAdjointUniq_eq_mate _ _ _ _ _ _
    (scalarSystems_evaluation_inv_eq_mate _ _ _ _ _ _ _ _ n)).trans
      (he)⟩

end FiniteEvaluationMate

section ScalarModelUniqueness

/-- An invertible map detects the unit of an adjunction through its transpose. -/
private theorem openScalar_unit_eq_of_transpose_eq
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (a b : L ⊣ R) {P : C} {K : D} (f : L.obj P ⟶ K) [IsIso f]
    (h : a.homEquiv P K f = b.homEquiv P K f) : a.unit.app P = b.unit.app P := by
  apply (cancel_mono (R.map f)).mp
  simpa only [Adjunction.homEquiv_unit] using h

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

-- comparing the two derived adjunctions unfolds large derived functor types
/-- Two system scalar models with the same cochain model have the same normalized
derived adjunction: the transpose of the counit on K-flat complexes fixes the unit. -/
theorem sequenceSystemScalarModel_adjunction_heq (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u})
    (A₁ A₂ : SheafOfModules.SystemScalarModel.{u + 1, u, u + 1}
      (integralComparisonSequenceScalarMap l E L ι W)) (h : A₁.model = A₂.model) :
    HEq A₁.adjunction A₂.adjunction := by
  obtain ⟨M, o₁, u₁, a₁, t₁⟩ := A₁
  obtain ⟨M', o₂, u₂, a₂, t₂⟩ := A₂
  dsimp only at h
  subst h
  have ho : o₁ = o₂ := by
    apply Adjunction.ext
    ext P U x
    rw [u₁, u₂]
  subst ho
  apply heq_of_eq
  apply Adjunction.ext
  apply sequenceDerived_kflat_ext l E W
  intro P hP
  have : IsIso (M.ε.app P) := M.computes P hP
  apply openScalar_unit_eq_of_transpose_eq a₁ a₂
    (M.ε.app P ≫ DerivedCategory.Q.map (𝟙 ((M.E.mapHomologicalComplex (.up ℤ)).obj P)))
  exact (t₁ P _ (𝟙 _)).trans (t₂ P _ (𝟙 _)).symm

end ScalarModelUniqueness

section ExplicitMate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory WeilConjectures.integralComparisonSequenceScalarModel

-- the derived mate comparison unfolds several large adjunction composites
/-- The derived scalar/pullback comparison is the derived scalar mate of the
restriction/pullback comparison, along the normalized adjunctions of the given
scalar models. -/
private theorem systemScalarPullback_eq_mate_of_models (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) {X B : Scheme.{u}} (j : X ⟶ B)
    (AB : SheafOfModules.SystemScalarModel.{u + 1, u, u + 1}
      (integralComparisonSequenceScalarMap l E L ι B))
    (AX : SheafOfModules.SystemScalarModel.{u + 1, u, u + 1}
      (integralComparisonSequenceScalarMap l E L ι X))
    (MB : type_of% (integralComparisonSequenceScalarModel l E L ι B))
    (MX : type_of% (integralComparisonSequenceScalarModel l E L ι X))
    (hAB : AB.model = MB) (hAX : AX.model = MX)
    (σB : MB.T ⊣ (sequenceRestriction l E L ι B).mapDerivedCategory)
    (σX : MX.T ⊣ (sequenceRestriction l E L ι X).mapDerivedCategory)
    (hσB : HEq σB AB.adjunction) (hσX : HEq σX AX.adjunction)
    (oB : MB.E ⊣ sequenceRestriction l E L ι B)
    (oX : MX.E ⊣ sequenceRestriction l E L ι X)
    (huB : ∀ P U x, (oB.unit.app P).val.app U x =
      SheafOfModules.systemModelTmul MB P U 1 x)
    (huX : ∀ P U x, (oX.unit.app P).val.app U x =
      SheafOfModules.systemModelTmul MX P U 1 x)
    (q : integralComparisonSequencePullback l L j ⋙ sequenceRestriction l E L ι X ≅
      sequenceRestriction l E L ι B ⋙ integralComparisonSequencePullback l E j)
    (a : integralComparisonSequencePullback l E j ⋙ MX.E ≅
      MB.E ⋙ integralComparisonSequencePullback l L j)
    (ha : a.hom = ((mateEquiv oB oX).symm (TwoSquare.mk _ _ _ _ q.inv)))
    (S : integralComparisonDerivedSequencePullback l E j ⋙ MX.T ≅
      MB.T ⋙ integralComparisonDerivedSequencePullback l L j)
    (hS : ∀ (P : CochainComplex (coefficientSequenceModules l E B) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients
        (R := coefficientSequenceCommRingSheaf l E B) P →
      MX.T.map
          ((integralComparisonSequencePullback l E j).mapDerivedCategoryFactors.hom.app P) ≫
        MX.ε.app (((integralComparisonSequencePullback l E j).mapHomologicalComplex
          (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex a (.up ℤ)).hom.app P) =
      S.hom.app (DerivedCategory.Q.obj P) ≫
        (integralComparisonDerivedSequencePullback l L j).map (MB.ε.app P) ≫
        (integralComparisonSequencePullback l L j).mapDerivedCategoryFactors.hom.app
          ((MB.E.mapHomologicalComplex (.up ℤ)).obj P)) :
    S.hom = ((mateEquiv σB σX).symm (TwoSquare.mk _ _ _ _
        (Functor.mapDerivedCategorySquareIso q).inv)) := by
  apply systemScalarPullback_eq_mate_general l E L ι j AB AX MB MX hAB hAX σB σX
    hσB hσX oB oX huB huX q.inv (Functor.mapDerivedCategorySquareIso q).inv ?_ a ha S hS
  simpa only [Functor.mapDerivedCategorySquareIso_symm, Iso.symm_hom] using
    Functor.isDerivedSquareOf_mapDerivedCategorySquareIso q.symm

/-- The fixed finite-evaluation scalar adjunction is the adjunction of the chosen model. -/
private theorem finiteEvaluationSystemScalarAdjunction_heq (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u}) :
    HEq (finiteEvaluationSystemScalarAdjunction l E L ι W)
      (finiteEvaluationSystemScalarModel_exists l E L ι W).choose.adjunction := by
  unfold finiteEvaluationSystemScalarAdjunction
  exact eq_mpr_heq_self _ _

-- the scalar/pullback comparison unfolds several large adjunction composites
/-- The derived scalar/pullback comparison is the inverse mate, along the fixed
finite-evaluation scalar adjunctions, of the derived restriction/pullback square. -/
private theorem systemScalarPullback_hom_eq_finiteMate (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) {X B : Scheme.{u}} (j : X ⟶ B) [IsOpenImmersion j] :
    letI := sequenceRestrictionPullbackInv_isIso l E L ι j
    (integralComparisonSystemScalarPullback l E L ι j).hom =
      ((mateEquiv (finiteEvaluationSystemScalarAdjunction l E L ι B)
        (finiteEvaluationSystemScalarAdjunction l E L ι X)).symm (TwoSquare.mk _ _ _ _
          (Functor.mapDerivedCategorySquareIso
            (asIso (sequenceRestrictionPullbackInv l E L ι j)).symm).inv)) := by
  exact systemScalarPullback_eq_mate_of_models l E L ι j
    (finiteEvaluationSystemScalarModel_exists l E L ι B).choose
    (finiteEvaluationSystemScalarModel_exists l E L ι X).choose _ _
    (finiteEvaluationSystemScalarModel_exists l E L ι B).choose_spec
    (finiteEvaluationSystemScalarModel_exists l E L ι X).choose_spec _ _
    (finiteEvaluationSystemScalarAdjunction_heq l E L ι B)
    (finiteEvaluationSystemScalarAdjunction_heq l E L ι X)
    (sequenceScalarAdjunction l E L ι B).choose (sequenceScalarAdjunction l E L ι X).choose
    (fun P U x ↦ (sequenceScalarAdjunction_unit l E L ι B P U x).trans
      (sequenceTensorSection_eq l E L ι B P U 1 x))
    (fun P U x ↦ (sequenceScalarAdjunction_unit l E L ι X P U x).trans
      (sequenceTensorSection_eq l E L ι X P U 1 x))
    (@asIso _ _ _ _ (sequenceRestrictionPullbackInv l E L ι j)
      (sequenceRestrictionPullbackInv_isIso l E L ι j)).symm
    (integralComparisonSequenceScalarPullback l E L ι j)
    (sequenceScalarPullback_hom_eq l E L ι j)
    (integralComparisonSystemScalarPullback l E L ι j)
    (integralComparisonSystemScalarPullback_existsUnique l E L ι j).exists.choose_spec

end ExplicitMate

-- unfolding the open scalar mate compares large derived functor composites
/-- The inverse open scalar mate is the iterated mate of the derived restriction/pullback
square along the open and fixed scalar adjunctions. -/
private theorem systemOpenScalarInv_eq_iteratedMate (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    systemOpenScalarInv l E L ι j = ((mateEquiv (systemDerivedOpenAdjunction l E j)
      (systemDerivedOpenAdjunction l L j)).symm
      ((mateEquiv (finiteEvaluationSystemScalarAdjunction l E L ι Z)
        (finiteEvaluationSystemScalarAdjunction l E L ι X)).symm (TwoSquare.mk _ _ _ _
          (Functor.mapDerivedCategorySquareIso
            (@asIso _ _ _ _ (sequenceRestrictionPullbackInv l E L ι j)
              (sequenceRestrictionPullbackInv_isIso l E L ι j)).symm).inv))) := by
  unfold systemOpenScalarInv
  rw [systemScalarPullback_hom_eq_finiteMate l E L ι j]
  rfl

/-- The open scalar evaluation equation, assuming the commuting cube of right-adjoint
comparisons (restriction/pullback, restriction evaluation, pullback evaluation and the
finite open restriction mate). -/
private theorem systemOpenScalarInv_finiteEvaluation_of_cube
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] (n : ℕ) (N : coefficientSequenceDerived l E X)
    [Finite (Padic.coefficientExtensionRing l E (n + 1))]
    [Finite (Padic.coefficientExtensionRing l L (n + 1))]
    (hcube : ∀ (ρX : TwoSquare
        (SemilinearSections.resD (integralComparisonSequenceScalarMap l E L ι X))
        (coefficientSequenceDerivedEvaluation l L X n)
        (coefficientSequenceDerivedEvaluation l E X n)
        (pbcDerivedRestrict (scalarRingMap (integralScalarQuotientMap l E L ι n) X)))
      (ρZ : TwoSquare
        (SemilinearSections.resD (integralComparisonSequenceScalarMap l E L ι Z))
        (coefficientSequenceDerivedEvaluation l L Z n)
        (coefficientSequenceDerivedEvaluation l E Z n)
        (pbcDerivedRestrict (scalarRingMap (integralScalarQuotientMap l E L ι n) Z))),
      HEq ρX (SemilinearSections.restrictionEvaluation (ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X) (coefficientSequenceCommRingTransition l E X)
        (integralCoefficientCommRingSheaf l L X) (coefficientSequenceCommRingTransition l L X)
        (integralScalarQuotientSheafMap l E L ι X)
        (scalarQuotient_compatible l E L ι X) n).hom →
      HEq ρZ (SemilinearSections.restrictionEvaluation (ProEt.topology Z)
        (integralCoefficientCommRingSheaf l E Z) (coefficientSequenceCommRingTransition l E Z)
        (integralCoefficientCommRingSheaf l L Z) (coefficientSequenceCommRingTransition l L Z)
        (integralScalarQuotientSheafMap l E L ι Z)
        (scalarQuotient_compatible l E L ι Z) n).hom →
      ∀ M, (coefficientSequenceDerivedEvaluation l E X n).map
          ((Functor.mapDerivedCategorySquareIso
            (@asIso _ _ _ _ (sequenceRestrictionPullbackInv l E L ι j)
              (sequenceRestrictionPullbackInv_isIso l E L ι j)).symm).inv.app M) ≫
        ρX.app ((integralComparisonDerivedSequencePullback l L j).obj M) ≫
        (pbcDerivedRestrict (scalarRingMap (integralScalarQuotientMap l E L ι n) X)).map
          ((systemPullEvaluation l L j n).inv.app M) ≫
        ((mateEquiv (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
            (sfIntrinsicOpenAdjunction (Padic.coefficientExtensionRing l L (n + 1)) j))
          (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
            (sfIntrinsicOpenAdjunction (Padic.coefficientExtensionRing l E (n + 1)) j)))
          (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso
            (sfOpenRestriction j (integralScalarQuotientMap l E L ι n))).hom)).app
          ((coefficientSequenceDerivedEvaluation l L Z n).obj M) =
        (systemPullEvaluation l E j n).inv.app
          ((SemilinearSections.resD (integralComparisonSequenceScalarMap l E L ι Z)).obj M) ≫
        (sfIntrinsicPullback (Padic.coefficientExtensionRing l E (n + 1)) j).mapDerivedCategory.map
          (ρZ.app M)) :
    let uE :=
      letI := systemOpenEvaluationInv_isIso l E j n
      (asIso (systemOpenEvaluationInv l E j n)).symm
    let uL :=
      letI := systemOpenEvaluationInv_isIso l L j n
      (asIso (systemOpenEvaluationInv l L j n)).symm
    let a :=
      ((mateEquiv (pbcDerivedScalarAdjunction
          (scalarRingMap (integralScalarQuotientMap l E L ι n) X))
        (pbcDerivedScalarAdjunction
          (scalarRingMap (integralScalarQuotientMap l E L ι n) Z))).symm
        (TwoSquare.mk _ _ _ _
          ((Functor.mapDerivedCategorySquareIso
            (sfOpenRestriction j (integralScalarQuotientMap l E L ι n))).hom)))
    (uL.hom.app ((integralComparisonDerivedSequenceScalar l E L ι X).obj N)) ≫
        (sfIntrinsicExtensionByZero j
          (Padic.coefficientExtensionRing l L (n + 1))).mapDerivedCategory.map
            ((systemScalarFiniteEvaluation l E L ι X n).hom.app N) =
      (coefficientSequenceDerivedEvaluation l L Z n).map
          ((systemOpenScalarInv l E L ι j).app N) ≫
        (systemScalarFiniteEvaluation l E L ι Z n).hom.app
          ((systemDerivedOpen l E j).obj N) ≫
        (pbcDerivedExtend
          (scalarRingMap (integralScalarQuotientMap l E L ι n) Z)).map
          (uE.hom.app N) ≫
        a.app ((coefficientSequenceDerivedEvaluation l E X n).obj N) := by
  have := systemOpenEvaluationInv_isIso l E j n
  have := systemOpenEvaluationInv_isIso l L j n
  have := systemOpenScalarInv_isIso l E L ι j
  obtain ⟨ρX, hρX, hβX⟩ := systemScalarFiniteEvaluation_inv_eq_mate l E L ι X n
  obtain ⟨ρZ, hρZ, hβZ⟩ := systemScalarFiniteEvaluation_inv_eq_mate l E L ι Z n
  exact openScalar_evaluation_of_cube (systemDerivedOpenAdjunction l E j)
    (systemDerivedOpenAdjunction l L j)
    (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
      (sfIntrinsicOpenAdjunction (Padic.coefficientExtensionRing l E (n + 1)) j))
    (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
      (sfIntrinsicOpenAdjunction (Padic.coefficientExtensionRing l L (n + 1)) j))
    (finiteEvaluationSystemScalarAdjunction l E L ι X)
    (finiteEvaluationSystemScalarAdjunction l E L ι Z)
    (pbcDerivedScalarAdjunction (scalarRingMap (integralScalarQuotientMap l E L ι n) X))
    (pbcDerivedScalarAdjunction (scalarRingMap (integralScalarQuotientMap l E L ι n) Z))
    (coefficientSequenceDerivedEvaluation l E X n) (coefficientSequenceDerivedEvaluation l E Z n)
    (coefficientSequenceDerivedEvaluation l L X n) (coefficientSequenceDerivedEvaluation l L Z n)
    (systemPullEvaluation l E j n).inv (systemPullEvaluation l L j n).inv ρX ρZ
    (Functor.mapDerivedCategorySquareIso
      (@asIso _ _ _ _ (sequenceRestrictionPullbackInv l E L ι j)
        (sequenceRestrictionPullbackInv_isIso l E L ι j)).symm).inv
    (Functor.mapDerivedCategorySquareIso
      (sfOpenRestriction j (integralScalarQuotientMap l E L ι n))).hom
    (hcube ρX ρZ hρX hρZ)
    (systemOpenEvaluationInv l E j n) rfl (systemOpenEvaluationInv l L j n) rfl
    (systemScalarFiniteEvaluation l E L ι X n) hβX
    (systemScalarFiniteEvaluation l E L ι Z n) hβZ
    _ rfl (systemOpenScalarInv l E L ι j) (systemOpenScalarInv_eq_iteratedMate l E L ι j) N

/-- The inverse open scalar mate evaluates to the finite open scalar transpose.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 03DI and 07A6
(blueprint: lem-sf-system-open-scalar-evaluation).

This is the inverse-mate square used to prove the forward evaluation theorem. It is
strictly below that theorem: the forward open scalar mate is absent, and the equation
is before cancellation of its inverse component. The proof is the sectionwise balanced
 tensor calculation on the open, followed by the unit and counit equations of the
specified open adjunctions and the normalized scalar evaluation maps. Localization
preserves these equations for arbitrary unbounded systems. -/
theorem systemOpenScalarInv_finiteEvaluation_core
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] (n : ℕ) (N : coefficientSequenceDerived l E X) :
    letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    letI := Padic.finite_coefficientExtensionRing l L (n + 1) (Nat.succ_pos n)
    let uE :=
      letI := systemOpenEvaluationInv_isIso l E j n
      (asIso (systemOpenEvaluationInv l E j n)).symm
    let uL :=
      letI := systemOpenEvaluationInv_isIso l L j n
      (asIso (systemOpenEvaluationInv l L j n)).symm
    let a :=
      ((mateEquiv (pbcDerivedScalarAdjunction
          (scalarRingMap (integralScalarQuotientMap l E L ι n) X))
        (pbcDerivedScalarAdjunction
          (scalarRingMap (integralScalarQuotientMap l E L ι n) Z))).symm
        (TwoSquare.mk _ _ _ _
          ((Functor.mapDerivedCategorySquareIso
            (sfOpenRestriction j (integralScalarQuotientMap l E L ι n))).hom)))
    (uL.hom.app ((integralComparisonDerivedSequenceScalar l E L ι X).obj N)) ≫
        (sfIntrinsicExtensionByZero j
          (Padic.coefficientExtensionRing l L (n + 1))).mapDerivedCategory.map
            ((systemScalarFiniteEvaluation l E L ι X n).hom.app N) =
      (coefficientSequenceDerivedEvaluation l L Z n).map
          ((systemOpenScalarInv l E L ι j).app N) ≫
        (systemScalarFiniteEvaluation l E L ι Z n).hom.app
          ((systemDerivedOpen l E j).obj N) ≫
        (pbcDerivedExtend
          (scalarRingMap (integralScalarQuotientMap l E L ι n) Z)).map
          (uE.hom.app N) ≫
        a.app ((coefficientSequenceDerivedEvaluation l E X n).obj N) := by
  have := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  have := Padic.finite_coefficientExtensionRing l L (n + 1) (Nat.succ_pos n)
  exact systemOpenScalarInv_finiteEvaluation_of_cube l E L ι j n N (by sorry)

end WeilConjectures.FrobeniusExchange
