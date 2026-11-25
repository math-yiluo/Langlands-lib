/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLocallyFreePullbackSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLatticeSumFree
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousLatticeSum
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteEtaleLatticeSheetMaps
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousFunctionPresentationRange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousFiniteEtaleSheetMatrices
import WeilConjectures.AlgebraicGeometry.LatticeMatrixNeighborhoods
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.LatticeSheafBasicSupplement
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Simultaneous continuous charts for embedded sheet lattices

Source: blueprint, stratified lattice trace proof, Local computation, paragraph 2.
(blueprint: lem-sfb-continuous-finite-etale-lattice-sheet-charts)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor Matrix

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] continuousRingModuleEquivalence
  finiteEtaleLatticeSheetEmbedding upperStar continuousFunctionPresentationRange

private def matrixFrame {E : Type} [Field E] {r : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin r) E) : (Fin r → E) ≃ₗ[E] (Fin r → E) :=
  (Matrix.GeneralLinearGroup.toLin g).toLinearEquiv

private theorem matrixFrame_inv {E : Type} [Field E] {r : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin r) E) :
    matrixFrame g⁻¹ = (matrixFrame g).symm := rfl

private def matrixFullLattice {E : Type} [Field E] (A : Subring E) {r : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin r) E) : Submodule A (Fin r → E) where
  carrier := {x | ∀ i, matrixFrame g⁻¹ x i ∈ A}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy i
    simpa only [map_add, Pi.add_apply] using A.add_mem (hx i) (hy i)
  smul_mem' := by
    intro a x hx i
    change matrixFrame g⁻¹ ((a : E) • x) i ∈ A
    simpa only [map_smul, Pi.smul_apply, smul_eq_mul] using A.mul_mem a.property (hx i)

private def matrixFullLatticeEquiv {E : Type} [Field E] (A : Subring E) {r : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin r) E) :
    (Fin r → A) ≃ₗ[A] matrixFullLattice A g where
  toFun a := ⟨matrixFrame g (fun i ↦ (a i : E)), by
    change ∀ i, matrixFrame g⁻¹ (matrixFrame g (fun i ↦ (a i : E))) i ∈ A
    rw [matrixFrame_inv, LinearEquiv.symm_apply_apply]
    exact fun i ↦ (a i).property⟩
  invFun x := fun i ↦ ⟨matrixFrame g⁻¹ x.val i, x.property i⟩
  left_inv a := by
    ext i
    change matrixFrame g⁻¹ (matrixFrame g (fun i ↦ (a i : E))) i = (a i : E)
    rw [matrixFrame_inv, LinearEquiv.symm_apply_apply]
  right_inv x := by
    apply Subtype.ext
    change matrixFrame g (matrixFrame g⁻¹ x.val) = x.val
    rw [matrixFrame_inv, LinearEquiv.apply_symm_apply]
  map_add' a b := by
    apply Subtype.ext
    change matrixFrame g (fun i ↦ ((a i : E) + (b i : E))) = _
    exact (matrixFrame g).map_add _ _
  map_smul' a x := by
    apply Subtype.ext
    change matrixFrame g ((a : E) • (fun i ↦ (x i : E))) = _
    exact (matrixFrame g).map_smul _ _

private theorem matrixFullLattice_basis {E : Type} [Field E] (A : Subring E) {r : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin r) E) :
    ∃ b : Module.Basis (Fin r) A (matrixFullLattice A g),
      ∃ c : Module.Basis (Fin r) E (Fin r → E), ∀ i, (b i : Fin r → E) = c i := by
  refine ⟨(Pi.basisFun A (Fin r)).map (matrixFullLatticeEquiv A g),
    (Pi.basisFun E (Fin r)).map (matrixFrame g), ?_⟩
  intro i
  simp only [Module.Basis.map_apply]
  change matrixFrame g (fun k ↦ ((Pi.basisFun A (Fin r) i k : A) : E)) = _
  congr 1
  ext k
  by_cases h : k = i <;> simp [Pi.basisFun_apply, h]

private theorem matrixFullLattice_mul_integral {E : Type} [Field E]
    (A : Subring E) {r : ℕ} (g : Matrix.GeneralLinearGroup (Fin r) E)
    (hg : ∀ i j, g.val i j ∈ A) (x : Fin r → E) (hx : ∀ i, x i ∈ A) :
    ∀ i, (g.val *ᵥ x) i ∈ A := by
  intro i
  change (∑ j, g.val i j * x j) ∈ A
  exact A.sum_mem (fun j _ ↦ A.mul_mem (hg i j) (hx j))

private theorem matrixFullLattice_eq_of_coset {E : Type} [Field E]
    (A : Subring E) {r : ℕ} (g h : Matrix.GeneralLinearGroup (Fin r) E)
    (he : (Quotient.mk _ g : integralMatrixCosets A r) = Quotient.mk _ h) :
    matrixFullLattice A g = matrixFullLattice A h := by
  have hm := (integralMatrixSubgroup_mem_iff E A r (g⁻¹ * h)).mp
    (QuotientGroup.leftRel_apply.mp (Quotient.exact he))
  have hmul (k q : Matrix.GeneralLinearGroup (Fin r) E) (x : Fin r → E) :
      (k * q).val *ᵥ x = k.val *ᵥ (q.val *ᵥ x) := Matrix.mulVec_mulVec .. |>.symm
  ext x
  constructor
  · intro hx
    have ht := matrixFullLattice_mul_integral A (g⁻¹ * h)⁻¹ hm.2
      ((g⁻¹).val *ᵥ x) hx
    change ∀ i, ((h⁻¹).val *ᵥ x) i ∈ A
    simpa only [← hmul, mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel, mul_one] using ht
  · intro hx
    have ht := matrixFullLattice_mul_integral A (g⁻¹ * h) hm.1
      ((h⁻¹).val *ᵥ x) hx
    change ∀ i, ((g⁻¹).val *ᵥ x) i ∈ A
    simpa only [← hmul, mul_assoc, mul_inv_cancel, mul_one] using ht

private theorem continuousLatticeInclusion_range {E : Type} [NormedField E]
    (A : Subring E) {r : ℕ} (L : Submodule A (Fin r → E))
    (Z : Type u) [TopologicalSpace Z] :
    Set.range (continuousLatticeInclusion A L Z) =
      {f : C(Z, Fin r → E) | ∀ z, f z ∈ L} := by
  ext f
  constructor
  · rintro ⟨x, rfl⟩ z
    exact (x z).property
  · intro hf
    exact ⟨⟨fun z ↦ ⟨f z, hf z⟩, f.continuous.subtype_mk _⟩, rfl⟩

private theorem isOpen_continuousIntegers (l : ℕ) [Fact l.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[l] E] :
    IsOpen (continuousIntegers l E : Set E) := by
  apply (continuousIntegers l E).toAddSubgroup.isOpen_of_mem_nhds (g := 0)
  apply Filter.mem_of_superset (Metric.ball_mem_nhds (0 : E) zero_lt_one)
  intro x hx
  have hnorm : ‖x‖ ≤ 1 := (by simpa only [Metric.mem_ball, dist_zero_right] using hx : ‖x‖ < 1).le
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[l]
  change x ∈ (NormedField.valuation (K := E)).integer
  change ‖x‖₊ ≤ 1
  exact_mod_cast hnorm

private theorem matrixLattices_neighborhood {E : Type} [NormedField E]
    (A : Subring E) (hA : IsOpen (A : Set E))
    {Y : Type u} [TopologicalSpace Y] (r d : ℕ)
    (G : Fin d → Y → Matrix.GeneralLinearGroup (Fin r) E)
    (hG : ∀ j i k, Continuous (fun y ↦ (G j y).val i k))
    (hGi : ∀ j i k, Continuous (fun y ↦ ((G j y)⁻¹).val i k)) (x : Y) :
    ∃ W : TopologicalSpace.Opens Y, x ∈ W ∧
      ∃ L : Fin d → Submodule A (Fin r → E),
        (∀ j, ∃ b : Module.Basis (Fin r) A (L j),
          ∃ c : Module.Basis (Fin r) E (Fin r → E), ∀ i, (b i : Fin r → E) = c i) ∧
        ∀ (j : Fin d) (Z : Type u) [TopologicalSpace Z] (a : Z → Y),
          (∀ z, a z ∈ W) →
          {f : C(Z, Fin r → E) | ∀ z i, (((G j (a z))⁻¹).val *ᵥ f z) i ∈ A} =
            Set.range (continuousLatticeInclusion A (L j) Z) := by
  classical
  have hn (j : Fin d) :=
    continuousMatrixCoset_neighborhood A hA r (G j) (hG j) (hGi j) x
  choose O hOx hO using hn
  let W : TopologicalSpace.Opens Y :=
    ⟨⋂ j : Fin d, (O j : Set Y), isOpen_iInter_of_finite (fun j ↦ (O j).isOpen)⟩
  refine ⟨W, Set.mem_iInter.mpr hOx, (fun j ↦ matrixFullLattice A (G j x)),
    (fun j ↦ matrixFullLattice_basis A (G j x)), ?_⟩
  intro j Z _ a ha
  refine Eq.trans ?_ (continuousLatticeInclusion_range A
    (matrixFullLattice A (G j x)) Z).symm
  ext f
  apply forall_congr'
  intro z
  have he := matrixFullLattice_eq_of_coset A (G j x) (G j (a z))
    (hO j _ (Set.mem_iInter.mp (ha z) j))
  change (∀ i, _) ↔ f z ∈ matrixFullLattice A (G j x)
  rw [he]
  rfl

private theorem matrixLattices_neighborhoods {E : Type} [NormedField E]
    (A : Subring E) (hA : IsOpen (A : Set E))
    {Y : Type u} [TopologicalSpace Y] (r d : ℕ)
    (G : Fin d → Y → Matrix.GeneralLinearGroup (Fin r) E)
    (hG : ∀ j i k, Continuous (fun y ↦ (G j y).val i k))
    (hGi : ∀ j i k, Continuous (fun y ↦ ((G j y)⁻¹).val i k)) :
    ∃ W : Y → TopologicalSpace.Opens Y, (∀ x, x ∈ W x) ∧
      ∃ L : Y → Fin d → Submodule A (Fin r → E),
        (∀ x j, ∃ b : Module.Basis (Fin r) A (L x j),
          ∃ c : Module.Basis (Fin r) E (Fin r → E), ∀ i, (b i : Fin r → E) = c i) ∧
        ∀ (x : Y) (j : Fin d) (Z : Type u) [TopologicalSpace Z] (a : Z → Y),
          (∀ z, a z ∈ W x) →
          {f : C(Z, Fin r → E) | ∀ z i, (((G j (a z))⁻¹).val *ᵥ f z) i ∈ A} =
            Set.range (continuousLatticeInclusion A (L x j) Z) := by
  classical
  have hn (x : Y) := matrixLattices_neighborhood A hA r d G hG hGi x
  choose W hx L hL hWL using hn
  exact ⟨W, hx, L, hL, hWL⟩

private theorem openCover_property {Y : Scheme.{u}}
    (W : Y → Y.Opens) (hx : ∀ x, x ∈ W x)
    (Q : ∀ Z : Scheme.{u}, (Z ⟶ Y) → Prop)
    (hQ : ∀ x, Q (W x).toScheme (W x).ι) :
    ∃ D : Scheme.Cover.{u} Scheme.proetalePrecoverage Y,
      ∀ k : D.I₀, Q (D.X k) (D.f k) := by
  let D : Scheme.Cover.{u} Scheme.zariskiPrecoverage Y :=
    Scheme.Cover.mkOfCovers Y (fun x ↦ (W x).toScheme) (fun x ↦ (W x).ι)
      (fun x ↦ ⟨x, ⟨x, hx x⟩, rfl⟩) (fun _ ↦ inferInstance)
  exact ⟨D.weaken Scheme.zariskiPrecoverage_le_proetalePrecoverage, hQ⟩

private theorem bindCover_property {X : Scheme.{u}}
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (Q : ∀ Y : Scheme.{u}, (Y ⟶ X) → Prop)
    (hQ : ∀ s : C.I₀, ∃ D : Scheme.Cover.{u} Scheme.proetalePrecoverage (C.X s),
      ∀ k : D.I₀, Q (D.X k) (D.f k ≫ C.f s)) :
    ∃ D : Scheme.Cover.{u} Scheme.proetalePrecoverage X,
      ∀ k : D.I₀, Q (D.X k) (D.f k) := by
  classical
  choose D hD using hQ
  exact ⟨C.bind D, fun s ↦ hD s.1 s.2⟩

private structure latticeSheetChart
    {E : Type} [NormedField E] (A : Subring E) {X U : Scheme.{u}} (p : U ⟶ X)
    (F : ∀ (Y : Scheme.{u}), (Y ⟶ X) → ℕ → Type v)
    (R : ∀ (Y : Scheme.{u}) (g : Y ⟶ X) (r : ℕ) (t : Y ⟶ U),
      (t ≫ p = g) → F Y g r → (B : Y.ProEt) → Set C(B.left, Fin r → E))
    (Y : Scheme.{u}) (g : Y ⟶ X) : Prop where
  chart :
    ∃ (r d : ℕ) (_ : 0 < d) (t : Fin d → (Y ⟶ U))
      (w : ∀ j, t j ≫ p = g),
      Nonempty (IsColimit (Cofan.mk (pullback p g)
        (fun j ↦ pullback.lift (t j) (𝟙 Y) (by simpa using w j)))) ∧
    ∃ L : Fin d → Submodule A (Fin r → E),
      (∀ j, ∃ b : Module.Basis (Fin r) A (L j),
        ∃ c : Module.Basis (Fin r) E (Fin r → E), ∀ i, (b i : Fin r → E) = c i) ∧
    ∃ c : F Y g r, ∀ (j : Fin d) (B : Y.ProEt),
      R Y g r (t j) (w j) c B = Set.range (continuousLatticeInclusion A (L j) B.left)

private theorem opens_ι_mem {Y : Scheme.{u}} (W : Y.Opens) (y : W.toScheme) :
    W.ι y ∈ W :=
  (le_of_eq W.range_ι : Set.range W.ι ⊆ (W : Set Y)) (Set.mem_range_self y)

private theorem matrixRange_on_open {E : Type} [NormedField E]
    (A : Subring E) {Y : Scheme.{u}} (r d : ℕ)
    (G : Fin d → Y → Matrix.GeneralLinearGroup (Fin r) E) (W : Y.Opens)
    (L : Fin d → Submodule A (Fin r → E))
    (hWL : ∀ (j : Fin d) (Z : Type u) [TopologicalSpace Z] (a : Z → Y),
      (∀ z, a z ∈ W) →
      {f : C(Z, Fin r → E) | ∀ z i, (((G j (a z))⁻¹).val *ᵥ f z) i ∈ A} =
        Set.range (continuousLatticeInclusion A (L j) Z))
    (j : Fin d) (B : W.toScheme.ProEt) :
    {f : C(B.left, Fin r → E) | ∀ z i,
      (((G j (W.ι (B.hom z)))⁻¹).val *ᵥ f z) i ∈ A} =
      Set.range (continuousLatticeInclusion A (L j) B.left) := by
  exact hWL j B.left (fun z ↦ W.ι (B.hom z)) (fun z ↦ opens_ι_mem W (B.hom z))

private theorem chart_on_open
    {E : Type} [NormedField E] (A : Subring E) {X U : Scheme.{u}} (p : U ⟶ X)
    (F : ∀ (Y : Scheme.{u}), (Y ⟶ X) → ℕ → Type v)
    (R : ∀ (Y : Scheme.{u}) (g : Y ⟶ X) (r : ℕ) (t : Y ⟶ U),
      (t ≫ p = g) → F Y g r → (B : Y.ProEt) → Set C(B.left, Fin r → E))
    (Y : Scheme.{u}) (g : Y ⟶ X)
    (r d : ℕ) (hd : 0 < d) (t : Fin d → (Y ⟶ U))
    (G : Fin d → Y → Matrix.GeneralLinearGroup (Fin r) E) (W : Y.Opens)
    (L : Fin d → Submodule A (Fin r → E))
    (hL : ∀ j, ∃ b : Module.Basis (Fin r) A (L j),
      ∃ c : Module.Basis (Fin r) E (Fin r → E), ∀ i, (b i : Fin r → E) = c i)
    (hW : ∃ w' : ∀ j, (W.ι ≫ t j) ≫ p = W.ι ≫ g,
      Nonempty (IsColimit (Cofan.mk (pullback p (W.ι ≫ g))
        (fun j ↦ pullback.lift (W.ι ≫ t j) (𝟙 W.toScheme)
          (by simpa using w' j)))) ∧
      ∃ c : F W.toScheme (W.ι ≫ g) r, ∀ (j : Fin d) (B : W.toScheme.ProEt),
        R W.toScheme (W.ι ≫ g) r (W.ι ≫ t j) (w' j) c B =
          {f : C(B.left, Fin r → E) | ∀ z i,
            (((G j (W.ι (B.hom z)))⁻¹).val *ᵥ f z) i ∈ A})
    (hWL : ∀ (j : Fin d) (Z : Type u) [TopologicalSpace Z] (a : Z → Y),
      (∀ z, a z ∈ W) →
      {f : C(Z, Fin r → E) | ∀ z i, (((G j (a z))⁻¹).val *ᵥ f z) i ∈ A} =
        Set.range (continuousLatticeInclusion A (L j) Z)) :
    latticeSheetChart A p F R W.toScheme (W.ι ≫ g) := by
  obtain ⟨w', hs, c, hc⟩ := hW
  refine ⟨⟨r, d, hd, (fun j ↦ W.ι ≫ t j), w', hs, L, hL, c, fun j B ↦ ?_⟩⟩
  exact (hc j B).trans (matrixRange_on_open A r d G W L hWL j B)

private theorem charts_of_cover
    {E : Type} [NormedField E] (A : Subring E) {X U : Scheme.{u}} (p : U ⟶ X)
    (F : ∀ (Y : Scheme.{u}), (Y ⟶ X) → ℕ → Type v)
    (R : ∀ (Y : Scheme.{u}) (g : Y ⟶ X) (r : ℕ) (t : Y ⟶ U),
      (t ≫ p = g) → F Y g r → (B : Y.ProEt) → Set C(B.left, Fin r → E))
    (h : ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X,
      ∀ s : C.I₀, latticeSheetChart A p F R (C.X s) (C.f s)) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
      ∃ (r d : ℕ) (_ : 0 < d) (t : Fin d → (C.X s ⟶ U))
        (w : ∀ j, t j ≫ p = C.f s),
        Nonempty (IsColimit (Cofan.mk (pullback p (C.f s))
          (fun j ↦ pullback.lift (t j) (𝟙 (C.X s)) (by simpa using w j)))) ∧
      ∃ L : Fin d → Submodule A (Fin r → E),
        (∀ j, ∃ b : Module.Basis (Fin r) A (L j),
          ∃ c : Module.Basis (Fin r) E (Fin r → E), ∀ i, (b i : Fin r → E) = c i) ∧
      ∃ c : F (C.X s) (C.f s) r, ∀ (j : Fin d) (B : (C.X s).ProEt),
        R (C.X s) (C.f s) r (t j) (w j) c B =
          Set.range (continuousLatticeInclusion A (L j) B.left) := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, fun s ↦ (hC s).chart⟩

/-- A finite family of sheet lattices becomes a family of fixed embedded full
algebraic lattices in one rational continuous-function chart. This statement
involves no trace morphism and no image of a sum.

Source: blueprint, stratified lattice trace proof, Local computation, paragraph 2;
Bhatt--Scholze, Section 6.8.
(blueprint: lem-sfb-continuous-finite-etale-lattice-sheet-charts)

Proof. Use continuousFiniteEtaleLattice_sheet_matrices to obtain a common
rational frame and continuous invertible matrices for the sheet embeddings.
The integral subring contains the open unit ball, hence is open. At each point,
the matrix-coset neighbourhood theorem gives a neighbourhood on which each
sheet matrix has constant integral right coset; intersect the finitely many
neighbourhoods. For the matrix at the point define L_j by inverse-coordinate
integrality. Multiplication by the matrix identifies A^r with L_j, and its
columns give both the integral basis and a rational basis. Integral change
matrices and their inverses preserve A^r, so equality of cosets identifies the
variable coordinate test with membership in this fixed lattice. Continuous
functions into a submodule are exactly the continuous vectors whose pointwise
values belong to it, by the induced topology. Apply this on every pro-etale
object in the open neighbourhood. The encoded actual sheet range is the range
definition's explicit formula. Form the open cover by these neighbourhoods,
weaken it to a pro-etale cover, and bind it with the matrix-coordinate cover.
The construction includes rank zero and empty schemes. No object is defined
by choosing a witness of an unproved existence statement. -/
theorem continuousFiniteEtaleLattice_sheet_charts
    (l : ℕ) [Fact l.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [TotallyDisconnectedSpace E] (X : Scheme.{u})
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hP : LocallyFree (condensedRingObj (Profinite.continuousMapRingObj E) X) P)
    {U : Scheme.{u}} (p : U ⟶ X) [IsFinite p] [Etale p] [Surjective p]
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (integralCoeff l E) U))
    (hM : LocallyFree (condensedRingObj (integralCoeff l E) U) M)
    (e : (Mod.extendScalars (coefficientMap (integralScalarMap l E) U)).obj M ≅
      (upperStar (Profinite.continuousMapRingObj E) p).obj P) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
      ∃ (r d : ℕ) (_ : 0 < d) (t : Fin d → (C.X s ⟶ U))
        (w : ∀ j, t j ≫ p = C.f s),
        Nonempty (IsColimit (Cofan.mk (pullback p (C.f s))
          (fun j ↦ pullback.lift (t j) (𝟙 (C.X s)) (by simpa using w j)))) ∧
      ∃ L : Fin d → Submodule (continuousIntegers l E) (Fin r → E),
        (∀ j, ∃ b : Module.Basis (Fin r) (continuousIntegers l E) (L j),
          ∃ c : Module.Basis (Fin r) E (Fin r → E), ∀ i, (b i : Fin r → E) = c i) ∧
      ∃ c : ContinuousFunctionPresentation (C.X s) (continuousIntegers l E) (Fin r → E)
          ((Mod.comap (coefficientMap (integralScalarMap l E) (C.X s))).obj
            ((upperStar (Profinite.continuousMapRingObj E) (C.f s)).obj P)),
        ∀ (j : Fin d) (B : (C.X s).ProEt),
          Set.range (fun x ↦ c.sections B
            (((continuousRingModuleEquivalence (C.X s) (continuousIntegers l E)).functor.map
              (finiteEtaleLatticeSheetEmbedding (integralScalarMap l E) P p M e
                (C.f s) (t j) (w j))).val.app (op B) x)) =
            Set.range (continuousLatticeInclusion (continuousIntegers l E) (L j) B.left) := by
  classical
  let F (Y : Scheme.{u}) (g : Y ⟶ X) (r : ℕ) :=
    ContinuousFunctionPresentation Y (continuousIntegers l E) (Fin r → E)
      ((Mod.comap (coefficientMap (integralScalarMap l E) Y)).obj
        ((upperStar (Profinite.continuousMapRingObj E) g).obj P))
  let R (Y : Scheme.{u}) (g : Y ⟶ X) (r : ℕ) (t : Y ⟶ U) (w : t ≫ p = g)
      (c : F Y g r) (B : Y.ProEt) : Set C(B.left, Fin r → E) :=
    continuousFunctionPresentationRange (continuousIntegers l E) c
      (finiteEtaleLatticeSheetEmbedding (integralScalarMap l E) P p M e g t w) B
  have h := charts_of_cover (continuousIntegers l E) p F R (by
    obtain ⟨C, hC⟩ := continuousFiniteEtaleLattice_sheet_matrices l E X P hP p M hM e
    apply bindCover_property C (latticeSheetChart (continuousIntegers l E) p F R)
    intro s
    obtain ⟨r, d, hd, t, w, G, hG, hGi, hW⟩ := hC s
    obtain ⟨W, hx, L, hL, hWL⟩ := matrixLattices_neighborhoods
      (continuousIntegers l E) (isOpen_continuousIntegers l E) r d G hG hGi
    let V (x : C.X s) : (C.X s).Opens := W x
    apply openCover_property V hx
      (fun Y f ↦ latticeSheetChart (continuousIntegers l E) p F R Y (f ≫ C.f s))
    intro x
    exact chart_on_open (continuousIntegers l E) p F R (C.X s) (C.f s) r d hd t G (V x)
      (L x) (hL x) (hW (V x)) (hWL x)
  )
  obtain ⟨C, hC⟩ := h
  refine ⟨C, ?_⟩
  intro s
  obtain ⟨r, d, hd, t, w, hs, L, hL, c, hc⟩ := hC s
  refine ⟨r, d, hd, t, w, hs, L, hL, c, ?_⟩
  intro j B
  exact (continuousFunctionPresentationRange_eq (continuousIntegers l E) c
    (finiteEtaleLatticeSheetEmbedding (integralScalarMap l E) P p M e
      (C.f s) (t j) (w j)) B).symm.trans (hc j B)

end AlgebraicGeometry.ProEtale.CondensedRing
