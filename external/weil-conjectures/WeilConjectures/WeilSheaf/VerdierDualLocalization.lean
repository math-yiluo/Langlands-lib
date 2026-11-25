/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.SmoothPuritySeparatedAdjunction

public import WeilConjectures.WeilSheaf.Localization
public import WeilConjectures.WeilSheaf.VerdierDual
public import WeilConjectures.WeilSheaf.LowerShriekFunctoriality
public import WeilConjectures.WeilSheaf.UpperStarLowerStar

/-!
# Verdier duality and the open–closed decomposition

Let `j : U ↪ X` be a quasi-compact open immersion with closed complement `i : Z ↪ X`. From the
statements of the duality theory of Weil complexes collected in
`WeilConjectures.WeilSheaf.VerdierDual`, this file derives the formal steps 1–4 of the proof of
the local boundary duality (`lemma-local-duality-point-c-u--1`):

1. `𝔻_X Rf_* G ≅ Rf₀! 𝔻 G` (Verdier exchange and biduality);
2. `Rf^! 𝔻_Y K ≅ 𝔻_X f^* K` (`Rf^! = 𝔻 f^* 𝔻` and biduality);
3. `Ri^! Rj₀! G ≅ (i^* Rj_* G)[-1]` (open–closed triangle, `j^* Rj_* = 𝟭`, and clause (4) of
   the localization theorem);
4. `𝔻_Z (i^* Rj_* G) ≅ (i^* Rj_* 𝔻_U G)[-1]`.

## Main statements

- `AlgebraicGeometry.WeilComplex.upperStarDerivedLowerStarIso`: `j^* Rj_* G ≅ G` for an open
  immersion `j`.
- `AlgebraicGeometry.WeilComplex.nonempty_verdierDual_upperStar_derivedLowerStar_iso`: step 4.
-/

@[expose] public section

-- The import of `WeilConjectures.WeilSheaf.Localization` brings in the instance
-- `AlgebraicGeometry.specOverSpec` of `(Spec A).Over (Spec R)` for an algebra, under which
-- `Spec k₀` would lie over itself through `Algebra.id` rather than through the identity, which the
-- structure-morphism instances `(X ↘ S).IsOver S` do not unify with. The canonical instance is
-- given priority.
attribute [instance 1100] CategoryTheory.instOverClass

universe u

open CategoryTheory Limits Opposite Pretriangulated

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilComplex

section UpperShriek

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [HasUpperShriek k₀ l f]

/-- The exceptional inverse image commutes with the shifts, as the right adjoint of the direct
image with compact support. -/
noncomputable instance : (upperShriek (k₀ := k₀) (l := l) f).CommShift ℤ :=
  (derivedLowerShriekUpperShriekAdjunction f).rightAdjointCommShift ℤ

/-- The exceptional inverse image is a triangulated functor, as the right adjoint of the
triangulated direct image with compact support. -/
instance : (upperShriek (k₀ := k₀) (l := l) f).IsTriangulated :=
  have := (derivedLowerShriekUpperShriekAdjunction (k₀ := k₀) (l := l) f).commShift_of_leftAdjoint
    ℤ
  (derivedLowerShriekUpperShriekAdjunction f).isTriangulated_rightAdjoint

end UpperShriek

section OpenRestriction

variable {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [X.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
  [j.IsOver (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- **The restriction of the derived direct image to the open**: for an open immersion
`j : U ↪ X`, `j^* Rj_* G ≅ G`. The pullback `j^*` is exact, so that
`j^* ∘ Rj_* ≅ R(j^* ∘ j_*)`, and `j^* ∘ j_* ≅ 𝟭` on pro-étale Weil sheaves. -/
noncomputable def upperStarDerivedLowerStarIso (G : WeilComplex k₀ l U) :
    (upperStar j).obj ((derivedLowerStar j).obj G) ≅ G :=
  ObjectProperty.isoMk _
    ((Functor.rightDerivedFunctorCompMapDerivedCategoryIso
        (ProEtaleWeilSheaf.lowerStar k₀ l j) (ProEtaleWeilSheaf.upperStar k₀ l j)).symm.app
        G.obj ≪≫
      (Functor.rightDerivedFunctorNatIso
        (ProEtaleWeilSheaf.lowerStarCompUpperStarIso k₀ l j)).app G.obj ≪≫
      (Functor.rightDerivedFunctorIsoMapDerivedCategory (𝟭 _)).app G.obj ≪≫
      (Functor.mapDerivedCategoryIdIso _).app G.obj)

end OpenRestriction

section Exchange

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [HasUpperShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))]
  [HasUpperShriek k₀ l (Y ↘ Spec (CommRingCat.of k₀))]

/-- **Step 1: the dual of a direct image** (blueprint: `lemma-local-duality-point-c-u--1`, step 1):
`𝔻_Y Rf_* G ≅ Rf₀! 𝔻_X G`. The Verdier exchange applied to `M = 𝔻_X G` and biduality on `X`
give `𝔻_Y Rf₀! 𝔻_X G ≅ Rf_* G`; applying `𝔻_Y` and biduality on `Y` gives the claim. -/
theorem nonempty_verdierDual_derivedLowerStar_iso (G : WeilComplex k₀ l X) :
    Nonempty ((verdierDual k₀ l Y).obj (op ((derivedLowerStar f).obj G)) ≅
      (derivedLowerShriek k₀ l f).obj ((verdierDual k₀ l X).obj (op G))) := by
  obtain ⟨e⟩ := nonempty_verdierDual_derivedLowerShriek_iso f ((verdierDual k₀ l X).obj (op G))
  obtain ⟨bX⟩ := nonempty_iso_verdierDual_rightOp_comp_verdierDual k₀ l X
  obtain ⟨bY⟩ := nonempty_iso_verdierDual_rightOp_comp_verdierDual k₀ l Y
  let e' : (verdierDual k₀ l Y).obj
      (op ((derivedLowerShriek k₀ l f).obj ((verdierDual k₀ l X).obj (op G)))) ≅
        (derivedLowerStar f).obj G :=
    e ≪≫ (derivedLowerStar f).mapIso (bX.app G).symm
  exact ⟨(verdierDual k₀ l Y).mapIso e'.op ≪≫ (bY.app _).symm⟩

variable [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]

/-- **Step 2: the exceptional inverse image of a dual** (blueprint:
`lemma-local-duality-point-c-u--1`, step 2): `Rf^! 𝔻_Y K ≅ 𝔻_X f^* K`, from `Rf^! = 𝔻_X f^* 𝔻_Y`
and biduality on `Y`. -/
theorem nonempty_upperShriek_verdierDual_iso [HasUpperShriek k₀ l f]
    (K : WeilComplex k₀ l Y) :
    Nonempty ((upperShriek f).obj ((verdierDual k₀ l Y).obj (op K)) ≅
      (verdierDual k₀ l X).obj (op ((upperStar f).obj K))) := by
  obtain ⟨e⟩ := nonempty_upperShriek_obj_iso f ((verdierDual k₀ l Y).obj (op K))
  obtain ⟨bY⟩ := nonempty_iso_verdierDual_rightOp_comp_verdierDual k₀ l Y
  exact ⟨e ≪≫ (verdierDual k₀ l X).mapIso ((upperStar f).mapIso (bY.app K)).op⟩

end Exchange

section ClosedImmersion

variable {U X Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [X.Over (Spec (CommRingCat.of k₀))] [Z.Over (Spec (CommRingCat.of k₀))]
  (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
  (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]

/-- The direct image with compact support `Ri₀! ≅ Ri_*` along a closed immersion is fully
faithful (`AlgebraicGeometry.WeilComplex.fullyFaithfulDerivedLowerStar`). -/
noncomputable def fullyFaithfulDerivedLowerShriekOfIsClosedImmersion :
    (derivedLowerShriek k₀ l i).FullyFaithful :=
  (fullyFaithfulDerivedLowerStar i).ofIso (derivedLowerShriekIsoDerivedLowerStar i).symm

/-- The direct image with compact support `Ri₀! ≅ Ri_*` along a closed immersion with an open
complement has a right adjoint, the exceptional inverse image `Ri^!`
(`AlgebraicGeometry.WeilComplex.isLeftAdjoint_derivedLowerStar`). -/
theorem hasUpperShriek_of_isCompl (hij : IsCompl (Set.range j.base) (Set.range i.base)) :
    HasUpperShriek k₀ l i :=
  have := isLeftAdjoint_derivedLowerStar (k₀ := k₀) (l := l) i j hij.symm
  Functor.isLeftAdjoint_of_iso (derivedLowerShriekIsoDerivedLowerStar i).symm

variable [HasUpperShriek k₀ l i]

/-- **The exceptional restriction of a direct image from the open complement vanishes**
(blueprint: `lemma-local-duality-point-c-u--1`, step 3, `Ri^! Rj_* G = 0`): for a closed immersion
`i` with open complement `j`, `Ri^! Rj_* G = 0`. For every `N` on `Z`,
`Hom(N, Ri^! Rj_* G) ≅ Hom(Ri₀! N, Rj_* G) ≅ Hom(i_* N, Rj_* G) = 0`, as `j^* i_* = 0`
(`AlgebraicGeometry.WeilComplex.subsingleton_hom_shift`). -/
theorem isZero_upperShriek_obj_derivedLowerStar_obj
    (hij : IsCompl (Set.range j.base) (Set.range i.base)) (G : WeilComplex k₀ l U) :
    IsZero ((upperShriek i).obj ((derivedLowerStar j).obj G)) := by
  set A := (upperShriek i).obj ((derivedLowerStar j).obj G)
  have : Subsingleton ((derivedLowerStar i).obj A ⟶ (derivedLowerStar j).obj G) := by
    have h := subsingleton_hom_shift (k₀ := k₀) (l := l) i j hij.symm A G 0
    exact @Equiv.subsingleton _ _
      (Iso.homCongr ((shiftFunctorZero _ ℤ).app _).symm (Iso.refl _)) h
  have : Subsingleton (A ⟶ A) :=
    (((derivedLowerShriekUpperShriekAdjunction i).homEquiv A _).symm.trans
      (Iso.homCongr ((derivedLowerShriekIsoDerivedLowerStar i).app A) (Iso.refl _))).subsingleton
  exact (IsZero.iff_id_eq_zero A).2 (Subsingleton.elim _ _)

/-- **The closed unit** (blueprint: `lemma-local-cohomology-right-adjoint--2`, clause (4), the unit
`Q ⟶ Ri^! i_* Q` is an isomorphism; `lemma-local-cohomology-right-adjoint--1`): for a closed
immersion `i`, the unit of the adjunction `Ri₀! ⊣ Ri^!` is an isomorphism, `Ri₀! ≅ Ri_*` being fully
faithful. -/
theorem isIso_derivedLowerShriekUpperShriekAdjunction_unit_app (Q : WeilComplex k₀ l Z) :
    IsIso ((derivedLowerShriekUpperShriekAdjunction (k₀ := k₀) (l := l) i).unit.app Q) := by
  have h := fullyFaithfulDerivedLowerShriekOfIsClosedImmersion (k₀ := k₀) (l := l) i
  have := h.full
  have := h.faithful
  have :=
    (derivedLowerShriekUpperShriekAdjunction (k₀ := k₀) (l := l) i).unit_isIso_of_L_fully_faithful
  infer_instance

end ClosedImmersion

section Localization

variable {U X Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [X.Over (Spec (CommRingCat.of k₀))] [Z.Over (Spec (CommRingCat.of k₀))]
  (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
  (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]

omit [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))] in
/-- **Step 3: the exceptional restriction of an extension by zero** (blueprint:
`lemma-local-duality-point-c-u--1`, step 3): for complementary immersions `j` and `i`,
`Ri^! Rj₀! G ≅ (i^* Rj_* G)[-1]`. Apply the triangulated functor `Ri^!` to the open–closed
triangle `Rj₀! j^* Rj_* G ⟶ Rj_* G ⟶ Ri_* i^* Rj_* G ⟶` of `Rj_* G`: the middle term becomes
`Ri^! Rj_* G = 0`, so the third arrow becomes an isomorphism, and the closed unit
`Q ≅ Ri^! Ri₀! Q` with `Ri₀! ≅ Ri_*` identifies the third term with `i^* Rj_* G`. -/
theorem nonempty_upperShriek_derivedLowerShriek_iso
    [HasUpperShriek k₀ l i] (hij : IsCompl (Set.range j.base) (Set.range i.base))
    (G : WeilComplex k₀ l U) :
    Nonempty ((upperShriek i).obj ((derivedLowerShriek k₀ l j).obj G) ≅
      ((upperStar i).obj ((derivedLowerStar j).obj G))⟦(-1 : ℤ)⟧) := by
  obtain ⟨T, hT, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ :=
    exists_distTriang_openClosed j i hij ((derivedLowerStar j).obj G)
  have hT' := (upperShriek i).map_distinguished T hT
  have h₂ : IsZero ((upperShriek i).obj T.obj₂) :=
    (isZero_upperShriek_obj_derivedLowerStar_obj j i hij G).of_iso ((upperShriek i).mapIso e₂)
  have := (Triangle.isZero₂_iff_isIso₃ _ hT').1 h₂
  let E : (upperShriek i).obj T.obj₃ ≅ ((upperShriek i).obj T.obj₁)⟦(1 : ℤ)⟧ :=
    asIso ((upperShriek i).mapTriangle.obj T).mor₃
  let Q := (upperStar i).obj ((derivedLowerStar j).obj G)
  have := isIso_derivedLowerShriekUpperShriekAdjunction_unit_app (k₀ := k₀) (l := l) i Q
  let v : Q ≅ (upperShriek i).obj ((derivedLowerShriek k₀ l i).obj Q) :=
    asIso ((derivedLowerShriekUpperShriekAdjunction i).unit.app Q)
  let e₃' : T.obj₃ ≅ (derivedLowerShriek k₀ l i).obj Q :=
    e₃ ≪≫ (derivedLowerShriekObjIsoDerivedLowerStar i Q).symm
  let e₁' : T.obj₁ ≅ (derivedLowerShriek k₀ l j).obj G :=
    e₁ ≪≫ (derivedLowerShriek k₀ l j).mapIso (upperStarDerivedLowerStarIso j G)
  let F₁ : ((upperShriek i).obj ((derivedLowerShriek k₀ l j).obj G))⟦(1 : ℤ)⟧ ≅ Q :=
    (shiftFunctor _ (1 : ℤ)).mapIso ((upperShriek i).mapIso e₁'.symm) ≪≫ E.symm ≪≫
      (upperShriek i).mapIso e₃' ≪≫ v.symm
  exact ⟨(shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by norm_num)).symm.app _ ≪≫
    (shiftFunctor _ (-1 : ℤ)).mapIso F₁⟩

variable [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))] [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [HasUpperShriek k₀ l (U ↘ Spec (CommRingCat.of k₀))]
  [HasUpperShriek k₀ l (Z ↘ Spec (CommRingCat.of k₀))]

/-- **Step 4: the dual of the boundary complex** (blueprint: `lemma-local-duality-point-c-u--1`,
step 4): for complementary immersions `j` and `i` and a Weil complex `G` on `U`,
`𝔻_Z (i^* Rj_* G) ≅ (i^* Rj_* 𝔻_U G)[-1]`. -/
theorem nonempty_verdierDual_upperStar_derivedLowerStar_iso
    (hij : IsCompl (Set.range j.base) (Set.range i.base)) (G : WeilComplex k₀ l U) :
    Nonempty ((verdierDual k₀ l Z).obj (op ((upperStar i).obj ((derivedLowerStar j).obj G))) ≅
      ((upperStar i).obj ((derivedLowerStar j).obj ((verdierDual k₀ l U).obj (op G))))⟦(-1 : ℤ)⟧)
    := by
  have := isLeftAdjoint_derivedLowerShriek_of_separated_base (k₀ := k₀) (l := l)
    (X ↘ Spec (CommRingCat.of k₀))
  have := hasUpperShriek_of_isCompl (k₀ := k₀) (l := l) j i hij
  obtain ⟨e₂⟩ := nonempty_upperShriek_verdierDual_iso i ((derivedLowerStar j).obj G)
  obtain ⟨e₁⟩ := nonempty_verdierDual_derivedLowerStar_iso j G
  obtain ⟨e₃⟩ := nonempty_upperShriek_derivedLowerShriek_iso j i hij
    ((verdierDual k₀ l U).obj (op G))
  exact ⟨e₂.symm ≪≫ (upperShriek i).mapIso e₁ ≪≫ e₃⟩

end Localization

section SmoothLisse

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- The tensor product of a lisse Weil sheaf `L` with a Weil sheaf `G` placed in degree zero is
the tensor product sheaf `L ⊗ G` placed in degree zero: the internal hom out of the lisse
`L^∨` is exact. -/
noncomputable def tensorLisseToComplexIso (L : WeilSheaf k₀ l X) (hL : L.IsLisse)
    (G : WeilSheaf k₀ l X) :
    (tensorLisse L hL).obj (WeilSheaf.toComplex.obj G) ≅
      WeilSheaf.toComplex.obj (L.tensorObj G hL) :=
  have := ProEtaleWeilSheaf.preservesFiniteColimits_ihomFunctor (L.dual hL).obj hL.dual
  ObjectProperty.isoMk _
    ((ProEtaleWeilSheaf.ihomFunctor k₀ l X (L.dual hL).obj).singleFunctorCompRightDerivedFunctorIso
      |>.app G.obj)

variable [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [HasUpperShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))]

/-- **The Verdier dual of a lisse sheaf on a smooth scheme** (blueprint:
`lemma-local-duality-point-c-u--1`, "`𝔻_U F ≅ F^∨(1)[2]`"): if `X` is smooth of pure dimension `d`
over `k₀` and `P` is a lisse Weil sheaf on `X`, then `𝔻_X P ≅ (P^∨ ⊗ (ℚ̄_ℓ(d) ⊗ ℚ̄_ℓ))[2d]`,
from `ω_X ≅ ℚ̄_ℓ(d)[2d]` and `RHom(P, N) ≅ P^∨ ⊗ N`. -/
theorem nonempty_verdierDual_toComplex_iso_of_isLisse (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
    (P : WeilSheaf k₀ l X) (hP : P.IsLisse) :
    Nonempty ((verdierDual k₀ l X).obj (op (WeilSheaf.toComplex.obj P)) ≅
      (WeilSheaf.toComplex.obj ((P.dual hP).tensorObj
        ((WeilSheaf.tateTwistSheaf k₀ l X d).tensorObj (WeilSheaf.adicConstant k₀ l X)
          (WeilSheaf.isLisse_tateTwistSheaf k₀ l X d)) hP.dual))⟦(2 * d : ℤ)⟧) := by
  obtain ⟨e₁⟩ := nonempty_tensorLisse_dual_iso_derivedHom P hP (dualizingComplex k₀ l X)
  obtain ⟨e₂⟩ := nonempty_dualizingComplex_iso (k₀ := k₀) (l := l) (X := X) d
  let T := tensorLisse (P.dual hP) hP.dual
  let E₁ : (verdierDual k₀ l X).obj (op (WeilSheaf.toComplex.obj P)) ≅
      T.obj (dualizingComplex k₀ l X) :=
    ObjectProperty.isoMk _ e₁.symm
  exact ⟨E₁ ≪≫ T.mapIso e₂ ≪≫ (T.commShiftIso (2 * d : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 * d : ℤ)).mapIso
      (T.mapIso (tensorLisseToComplexIso (WeilSheaf.tateTwistSheaf k₀ l X d)
        (WeilSheaf.isLisse_tateTwistSheaf k₀ l X d) _) ≪≫ tensorLisseToComplexIso _ _ _)⟩

end SmoothLisse

end WeilComplex

end AlgebraicGeometry
