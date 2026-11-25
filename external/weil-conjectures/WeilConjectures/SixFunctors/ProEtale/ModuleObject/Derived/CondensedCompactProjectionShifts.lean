/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
public import WeilConjectures.PoincareDuality.ProjectionFormulaShift

/-!
# Native condensed compact-support projection and shifts

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-package/
fix-lem-tensor-adjunction.proof.md, Step 1 and the final shift assertion
(blueprint: lem-sf-condensed-compact-projection-shifts).

The projection is the published counit-defined proper projection followed by the inverse
open projection comparison and the pullback compositor. Tensor and shift structures are
those of the ordinary relative K-flat derived category, including the signed second slot.
The four coefficient cases are specified up to isomorphism of condensed rings. Finite
extensions are represented by finite intermediate fields in the fixed standard closure;
this does not impose a choice of model on the input condensed ring.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option maxRecDepth 4096 in
-- Native derived-functor instance expressions are large.
-- Allow elaboration of the two explicit geometric shift squares.
/-- The actual compactification-defined projection commutes separately with every integer
shift of either finite-Tor input, using the native signed tensor comparisons and the
unit/counit-compatible derived-adjoint comparisons. The two equalities are the squares
`τ_[r] ≫ s_G = s_F ≫ τ[r]`, in Lean's left-to-right composition convention.

Source: latest blueprint, fix-lem-tensor-adjunction.proof.md, Step 1 (inverse projection)
and final shift assertion (blueprint: lem-sf-condensed-compact-projection-shifts).

Proof:
1. First variable, for fixed `L`. Put `I = Di_!`, `G = Rp_*`, `V = Li^*` for `c = (i, p)`,
and `N = Lp^* L`. The first-variable transformation `β` induced by the lax tensor map of `V`
is, by `Functor.Monoidal.δ_μ` after cancelling the invertible tensor comparison, the inverse
of `Adjunction.comparisonFlipApp (leftDerivedUpperStarTensor Λ i) N`; the native tensor
comparison commutes with shifts, hence so does `β`. The open adjunction `I ⊣ V` commutes
with shifts (`commShift_derivedOpenImmersionLowerShriekUpperStarAdjunction_ofNatIsoRight`),
so `Adjunction.commShift_projectionMapFlipApp` gives the shift compatibility of its projection
map `q`, which is `openImmersionProjectionComparison` (`openImmersionProjectionComparison_eq`)
and hence invertible; so `inv q` commutes with shifts.
2. The transformation `τ` obtained by whiskering the proper projection (`projectionMap Λ p`,
shift-compatible by `commShift_projectionMap_flipApp`) by `I`, then `inv q` by `G`, then the
tensor with the compositor component `(leftDerivedUpperStarCompactificationIso Λ c).inv.app L`
by `I ⋙ G`, with the associators, commutes with shifts by composition and whiskering
(lem-weil-pbc-commshift-nattrans-comp-whisker). Its components are
`exceptionalProjectionMorphismOfCompactification Λ c K L`; `NatTrans.shift_app_comm`
gives the first square.
3. Second variable: `NatTrans.shift_app_comm` applied to
`exceptionalProjectionMorphismOfCompactificationNatTrans Λ c K`, which commutes with shifts by
`commShift_exceptionalProjectionMorphismOfCompactificationNatTrans`.
Both arguments hold in the ambient derived categories for every commutative condensed ring;
the coefficient hypothesis and the finite-Tor restriction of the inputs are not used. -/
theorem condensedCompactProjection_shifts
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (_hΛ :
      (∃ (E : PadicAlgCl.FiniteIntermediateField C.l)
        (π : PadicAlgCl.integers C.l E) (m : ℕ),
        Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers C.l E) ∧
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj
          (completedResidue C.l E π m)))) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField C.l,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj C.l E))) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField C.l,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj C.l)))
    {X Y : Over (Spec (CommRingCat.of D.k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (c : Compactification f.left)
    (K : ConstantModelConstructibleFiniteTor Λ X.left)
    (L : ConstantModelConstructibleFiniteTor Λ Y.left) (r : ℤ) :
    (exceptionalProjectionMorphismOfCompactification Λ c (K.obj⟦r⟧) L.obj ≫
        (((curriedTensor _).flip.obj ((L((f.left)^*⟦Λ⟧)).obj L.obj) ⋙
          Rf_!(c)⟦Λ⟧).commShiftIso r).hom.app K.obj =
      ((Rf_!(c)⟦Λ⟧ ⋙ (curriedTensor _).flip.obj L.obj).commShiftIso r).hom.app K.obj ≫
        (shiftFunctor _ r).map
          (exceptionalProjectionMorphismOfCompactification Λ c K.obj L.obj)) ∧
    (exceptionalProjectionMorphismOfCompactification Λ c K.obj (L.obj⟦r⟧) ≫
        (((L((f.left)^*⟦Λ⟧) ⋙ (curriedTensor _).obj K.obj) ⋙
          Rf_!(c)⟦Λ⟧).commShiftIso r).hom.app L.obj =
      (((curriedTensor _).obj ((Rf_!(c)⟦Λ⟧).obj K.obj)).commShiftIso r).hom.app L.obj ≫
        (shiftFunctor _ r).map
          (exceptionalProjectionMorphismOfCompactification Λ c K.obj L.obj)) := by
  -- The native source library already supplies the proper projection's two shift squares.
  -- Only the first-variable open mate and the pasting of the actual factors remain.
  constructor
  · let I := D((c.i)_!open⟦Λ⟧)
    let G := R((c.g)_*⟦Λ⟧)
    let V := L((c.i)^*⟦Λ⟧)
    let N := (L((c.g)^*⟦Λ⟧)).obj L.obj
    let δ := Functor.LaxMonoidal.μNatTrans V
    let β := Adjunction.comparisonFlipApp' V (curriedTensor _) (curriedTensor _) δ N
    have : IsIso (Adjunction.comparisonFlipApp (leftDerivedUpperStarTensor Λ c.i) N) := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro A
      change IsIso (((leftDerivedUpperStarTensor Λ c.i).app A).app N)
      infer_instance
    have hβ : β = (asIso
        (Adjunction.comparisonFlipApp (leftDerivedUpperStarTensor Λ c.i) N)).inv := by
      ext A
      rw [← cancel_epi (((leftDerivedUpperStarTensor Λ c.i).app A).app N)]
      exact (Functor.Monoidal.δ_μ V A N).trans
        ((asIso (Adjunction.comparisonFlipApp
          (leftDerivedUpperStarTensor Λ c.i) N)).hom_inv_id_app A).symm
    have : NatTrans.CommShift β ℤ := by
      rw [hβ]
      exact NatTrans.CommShift.of_iso_inv _ ℤ
    let adj := derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ c.i
    have : adj.CommShift ℤ :=
      commShift_derivedOpenImmersionLowerShriekUpperStarAdjunction_ofNatIsoRight Λ c.i
    let q := adj.projectionMapFlipApp V (curriedTensor _) (curriedTensor _) δ N
    have : NatTrans.CommShift q ℤ :=
      Adjunction.commShift_projectionMapFlipApp adj V _ _ δ ℤ N
    have hq (A) : q.app A = openImmersionProjectionComparison Λ c.i A N := by
      exact (openImmersionProjectionComparison_eq Λ c.i A N).symm
    have : IsIso q := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro A
      rw [hq]
      infer_instance
    have : NatTrans.CommShift (inv q) ℤ :=
      NatTrans.CommShift.of_iso_inv (asIso q) ℤ
    let pm : G ⋙ (curriedTensor _).flip.obj L.obj ⟶
        (curriedTensor _).flip.obj N ⋙ G :=
      NatTrans.flipApp (projectionMap Λ c.g) L.obj
    have : NatTrans.CommShift pm ℤ := commShift_projectionMap_flipApp Λ c.g L.obj
    let e := (leftDerivedUpperStarCompactificationIso Λ c).inv.app L.obj
    let t := (curriedTensor _).flip.map e
    have : NatTrans.CommShift t ℤ := inferInstance
    let τ : Rf_!(c)⟦Λ⟧ ⋙ (curriedTensor _).flip.obj L.obj ⟶
        (curriedTensor _).flip.obj ((L((f.left)^*⟦Λ⟧)).obj L.obj) ⋙ Rf_!(c)⟦Λ⟧ :=
      (Functor.associator I G _).hom ≫
        Functor.whiskerLeft I pm ≫
        (Functor.associator I _ G).inv ≫
        Functor.whiskerRight (inv q) G ≫
        (Functor.associator _ I G).hom ≫
        Functor.whiskerRight t (I ⋙ G)
    have : NatTrans.CommShift τ ℤ := inferInstance
    have hτ (A) : τ.app A =
        exceptionalProjectionMorphismOfCompactification Λ c A L.obj := by
      simp only [τ, NatTrans.comp_app, Functor.associator_hom_app,
        Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Category.id_comp]
      erw [Category.id_comp, Category.id_comp]
      change pm.app (I.obj A) ≫ G.map ((inv q).app A) ≫ G.map (I.map (t.app A)) = _
      rw [← G.map_comp]
      change _ = properProjectionMorphism Λ c.g (I.obj A) L.obj ≫ _
      congr 1
      congr 1
      simp only [NatIso.isIso_inv_app, hq]
      rfl
    simpa only [hτ] using (NatTrans.shift_app_comm τ r K.obj).symm
  · exact (NatTrans.shift_app_comm
      (exceptionalProjectionMorphismOfCompactificationNatTrans Λ c K.obj) r L.obj).symm

end AlgebraicGeometry.ProEtale.CondensedRing
