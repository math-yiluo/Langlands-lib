/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PairHenselization
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.Algebra.Ring.Idempotent
public import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.RingTheory.PairHenselizationFiltered
import WeilConjectures.RingTheory.PairHenselizationEssentiallySmall
import WeilConjectures.RingTheory.FilteredEtaleFiberStructure
import WeilConjectures.RingTheory.FibrePrimesResidueFields
import WeilConjectures.RingTheory.FibreRingNoetherian
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.TensorProduct.Pi

/-!
# The idempotent selecting a pair henselization fibre component

Source: Stacks Project, More on Algebra, Tags 0AH1 and 0AH3.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace RingTheory

/-- Transport the reduced, zero-dimensional fibre structure to the given cocone. -/
private theorem pair_fiber_structure
    (A : Type u) [CommRing A] (I : Ideal A)
    (c : Cocone (ObjectProperty.ι
      (fun D : Under (CommRingCat.of A) ↦
        AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map D.hom) ∧
          Function.Bijective (Ideal.quotientMap (I.map D.hom.hom) D.hom.hom
            (Ideal.le_comap_map)))))
    (hc : IsColimit c) (p : PrimeSpectrum A) :
    letI := c.pt.hom.hom.toAlgebra
    IsReduced (p.asIdeal.Fiber c.pt.right) ∧
      Ring.KrullDimLE 0 (p.asIdeal.Fiber c.pt.right) := by
  open scoped TensorProduct in
  classical
  let := c.pt.hom.hom.toAlgebra
  dsimp only
  let P : ObjectProperty (Under (CommRingCat.of A)) := fun D ↦
    AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map D.hom) ∧
      Function.Bijective (Ideal.quotientMap (I.map D.hom.hom) D.hom.hom
        Ideal.le_comap_map)
  let : EssentiallySmall.{u} P.FullSubcategory := pair_henselization_essentiallySmall A I
  let : IsFiltered P.FullSubcategory := pair_henselization_filtered A I
  let E := equivSmallModel.{u} P.FullSubcategory
  let : IsFiltered (SmallModel.{u} P.FullSubcategory) := IsFiltered.of_equivalence E
  let U := (commAlgCatEquivUnder (CommRingCat.of A)).inverse
  let D := E.inverse ⋙ P.ι ⋙ U
  let d : Cocone D := U.mapCocone (c.whisker E.inverse)
  have hd : IsColimit d := isColimitOfPreserves U (hc.whiskerEquivalence E.symm)
  let e : c.pt.right ≃ₐ[A] ↥(colimit D) := CommAlgCat.algEquivOfIso
    (hd.coconePointUniqueUpToIso (colimit.isColimit D))
  have het : ∀ i, Algebra.Etale A (D.obj i) := by
    intro i
    exact (AlgebraicGeometry.HasRingHomProperty.Spec_iff
      (P := @AlgebraicGeometry.Etale)).mp (E.inverse.obj i).property.1
  obtain ⟨hr, hk⟩ := CommAlgCat.filteredEtale_fiber_structure A D het p
  let : IsReduced (p.asIdeal.Fiber ↥(colimit D)) := hr
  let : Ring.KrullDimLE 0 (p.asIdeal.Fiber ↥(colimit D)) := hk
  let t : p.asIdeal.Fiber c.pt.right ≃ₐ[A] p.asIdeal.Fiber ↥(colimit D) :=
    Algebra.TensorProduct.congr
      (AlgEquiv.refl : p.asIdeal.ResidueField ≃ₐ[A] p.asIdeal.ResidueField) e
  refine ⟨isReduced_of_injective t t.injective, ?_⟩
  apply Ring.krullDimLE_iff.mpr
  rw [ringKrullDim_eq_of_ringEquiv t.toRingEquiv]
  exact Ring.krullDimLE_iff.mp hk

/-- The canonical residue map is the product decomposition of an Artinian reduced fibre. -/
private theorem fiber_product_bijective
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (p : PrimeSpectrum A) [IsReduced (p.asIdeal.Fiber B)]
    [IsArtinianRing (p.asIdeal.Fiber B)] :
    let F := PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p}
    let ψ : (q : F) → p.asIdeal.Fiber B →+* q.1.asIdeal.ResidueField := fun q ↦
      (Algebra.TensorProduct.lift
        (Ideal.ResidueField.mapₐ p.asIdeal q.1.asIdeal (Algebra.ofId A B)
          congr($(q.2.symm).asIdeal))
        (IsScalarTower.toAlgHom A B q.1.asIdeal.ResidueField)
        (fun _ _ ↦ Commute.all _ _)).toRingHom
    Finite F ∧ Function.Bijective (RingHom.pi ψ) := by
  open scoped TensorProduct in
  classical
  dsimp only
  let K := p.asIdeal.Fiber B
  let F := PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p}
  let ψ : (q : F) → K →+* q.1.asIdeal.ResidueField := fun q ↦
    (Algebra.TensorProduct.lift
      (Ideal.ResidueField.mapₐ p.asIdeal q.1.asIdeal (Algebra.ofId A B)
        congr($(q.2.symm).asIdeal))
      (IsScalarTower.toAlgHom A B q.1.asIdeal.ResidueField)
      (fun _ _ ↦ Commute.all _ _)).toRingHom
  obtain ⟨e, _, _, hθ⟩ := PrimeSpectrum.fibre_primes_residue_fields A B p
  let : Finite F := Finite.of_equiv (PrimeSpectrum K) e.toEquiv
  refine ⟨inferInstance, ?_⟩
  let eM : MaximalSpectrum K ≃ F :=
    IsArtinianRing.primeSpectrumEquivMaximalSpectrum.symm.trans e.toEquiv
  let θ (q : F) := (hθ q).choose
  have hθ' (q : F) := (hθ q).choose_spec
  let g (q : F) : (K ⧸ (eM.symm q).asIdeal) ≃+* q.1.asIdeal.ResidueField := by
    change (K ⧸ (e.symm q).asIdeal) ≃+* q.1.asIdeal.ResidueField
    exact (RingEquiv.ofBijective
      (algebraMap (K ⧸ (e.symm q).asIdeal) (e.symm q).asIdeal.ResidueField)
      ((e.symm q).asIdeal.bijective_algebraMap_quotient_residueField)).trans (θ q)
  let E := (IsArtinianRing.equivPi K).toRingEquiv.trans
    ((RingEquiv.piCongrLeft' (fun m : MaximalSpectrum K ↦ K ⧸ m.asIdeal) eM).trans
      (RingEquiv.piCongrRight g))
  have hE : E.toRingHom = RingHom.pi ψ := by
    apply RingHom.ext
    intro x
    funext q
    change θ q (algebraMap (K ⧸ (e.symm q).asIdeal)
      (e.symm q).asIdeal.ResidueField (Ideal.Quotient.mk _ x)) = ψ q x
    rw [Ideal.algebraMap_quotient_residueField_mk]
    exact congrArg (fun f : K →+* q.1.asIdeal.ResidueField ↦ f x) (hθ' q)
  rw [← hE]
  exact E.bijective

/-- A coordinate of a product decomposition has an idempotent kernel annihilator. -/
private theorem fiber_projection_of_product_equiv
    {X Y ι : Type*} [CommRing X] [CommRing Y]
    {K : ι → Type*} [∀ i, CommRing (K i)] (j : ι)
    (T : X ≃+* ((i : ι) → K i)) (Q : K j ≃+* Y) (φ : X →+* Y)
    (hcoord : ∀ z, Q (T z j) = φ z) :
    ∃ e : X, IsIdempotentElem e ∧ φ e = 1 ∧
      Function.Surjective φ ∧ ∀ x, φ x = 0 → e * x = 0 := by
  classical
  let ε : (i : ι) → K i := Pi.single j 1
  refine ⟨T.symm ε, ?_, ?_, ?_, ?_⟩
  · apply T.injective
    change T (T.symm ε * T.symm ε) = T (T.symm ε)
    simp only [map_mul, T.apply_symm_apply]
    funext i
    by_cases h : i = j
    · subst i
      simp [ε]
    · simp [ε, Pi.single_eq_of_ne h]
  · rw [← hcoord, T.apply_symm_apply]
    simp [ε]
  · intro z
    refine ⟨T.symm (Pi.single j (Q.symm z)), ?_⟩
    rw [← hcoord, T.apply_symm_apply]
    simp
  · intro x hx
    have hxj : T x j = 0 := Q.injective (by rw [hcoord, hx, map_zero])
    apply T.injective
    simp only [map_mul, T.apply_symm_apply, map_zero]
    funext i
    by_cases h : i = j
    · subst i
      simp [ε, hxj]
    · simp [ε, Pi.single_eq_of_ne h]

/-- The canonical map of fibres is a surjective projection with idempotent kernel annihilator.

Source: Stacks Project, More on Algebra, Tag 0AH1 and the product calculation in Tag 0AH3.
(blueprint: lem-weil-pbc-pair-henselization-fiber-projection).

Proof: Filteredness and essential smallness of the pair-etale category allow its
colimit to be represented by a small filtered diagram of commutative A-algebras.
The reduced, zero-dimensional fibre statement of Tag 0AH1, together with
Noetherianity, makes the fibre Artinian. Its canonical Artinian product decomposition
and the fibre residue-field identifications give the residue fields at primes above p.
Each component sends x tensor b to rho(x) times
the image of b. Thus this ring equivalence respects the c.pt.right-algebra structures
(on the source through the second tensor factor), so it can be tensored over
c.pt.right with C.
Tensor cancellation and distribution over a finite product identify p.Fiber C with
that product of fibres. On pure tensors its q projection is exactly phi by the
specified compatibility, so equality on all tensors follows by additive generation.
In that product select the element equal to one at q and zero elsewhere and pull it
back to an element e of p.Fiber C. Componentwise multiplication proves idempotence
and phi(e)=1. Extend any element in the q factor by zero to prove surjectivity.
A kernel element has zero q coordinate, so multiplication by e kills it in every
coordinate. The argument also works when the q factor is the zero ring. The given
prime q supplies an index even if other fibres are empty. -/
theorem pair_henselization_fiber_projection
    (A : Type u) [CommRing A] (I : Ideal A)
    (c : Cocone (ObjectProperty.ι
      (fun D : Under (CommRingCat.of A) ↦
        AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map D.hom) ∧
          Function.Bijective (Ideal.quotientMap (I.map D.hom.hom) D.hom.hom
            (Ideal.le_comap_map)))))
    (hc : IsColimit c) [IsNoetherianRing c.pt.right]
    (C : Type u) [CommRing C] (g : c.pt.right →+* C)
    (q : Ideal c.pt.right) [q.IsPrime] :
    letI := c.pt.hom.hom.toAlgebra
    letI := g.toAlgebra
    letI := (g.comp c.pt.hom.hom).toAlgebra
    letI : IsScalarTower A c.pt.right C :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    let p := q.comap c.pt.hom.hom
    ∀ (ρ : p.ResidueField →ₐ[A] q.ResidueField),
      ρ = Ideal.ResidueField.mapₐ p q (Algebra.ofId A c.pt.right) rfl →
    ∀ (φ : p.Fiber C →+* q.Fiber C),
      (∀ (x : p.ResidueField) (y : C),
        φ (TensorProduct.tmul A x y) = TensorProduct.tmul c.pt.right (ρ x) y) →
      ∃ e : p.Fiber C, IsIdempotentElem e ∧ φ e = 1 ∧
        Function.Surjective φ ∧ ∀ x, φ x = 0 → e * x = 0 := by
  open scoped TensorProduct in
  classical
  let := c.pt.hom.hom.toAlgebra
  let := g.toAlgebra
  let := (g.comp c.pt.hom.hom).toAlgebra
  let : IsScalarTower A c.pt.right C :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  intro p' ρ hρ φ hφ
  subst ρ
  let B := c.pt.right
  let p : PrimeSpectrum A := ⟨q.comap c.pt.hom.hom, inferInstance⟩
  have hs := pair_fiber_structure A I c hc p
  obtain ⟨hr, hk⟩ := hs
  let : IsReduced (p.asIdeal.Fiber B) := hr
  let : Ring.KrullDimLE 0 (p.asIdeal.Fiber B) := hk
  let : IsNoetherianRing (p.asIdeal.Fiber B) := Ideal.isNoetherianRing_fiber p.asIdeal
  let : IsArtinianRing (p.asIdeal.Fiber B) :=
    IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  let F := PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p}
  let ψ : (r : F) → p.asIdeal.Fiber B →+* r.1.asIdeal.ResidueField := fun r ↦
    (Algebra.TensorProduct.lift
      (Ideal.ResidueField.mapₐ p.asIdeal r.1.asIdeal (Algebra.ofId A B)
        congr($(r.2.symm).asIdeal))
      (IsScalarTower.toAlgHom A B r.1.asIdeal.ResidueField)
      (fun _ _ ↦ Commute.all _ _)).toRingHom
  have hb : Finite F ∧ Function.Bijective (RingHom.pi ψ) :=
    @fiber_product_bijective A B _ _ c.pt.hom.hom.toAlgebra p hr
      (IsNoetherianRing.isArtinianRing_of_krullDimLE_zero :
        IsArtinianRing (p.asIdeal.Fiber B))
  obtain ⟨hfin, hbij⟩ := hb
  let : Finite F := hfin
  let : Fintype F := Fintype.ofFinite F
  let q₀ : F := ⟨⟨q, inferInstance⟩, rfl⟩
  let e₀ := RingEquiv.ofBijective (RingHom.pi ψ) hbij
  let E : (B ⊗[A] p.asIdeal.ResidueField) ≃ₐ[B]
      ((r : F) → r.1.asIdeal.ResidueField) :=
    { toRingEquiv := (Algebra.TensorProduct.comm A B p.asIdeal.ResidueField).toRingEquiv
        |>.trans e₀
      commutes' := by
        intro b
        funext r
        change (Ideal.ResidueField.mapₐ p.asIdeal r.1.asIdeal (Algebra.ofId A B)
          congr($(r.2.symm).asIdeal)) 1 * algebraMap B r.1.asIdeal.ResidueField b = _
        simp }
  let T : p.asIdeal.Fiber C ≃+* ((r : F) → C ⊗[B] r.1.asIdeal.ResidueField) :=
    (Algebra.TensorProduct.comm A p.asIdeal.ResidueField C).toRingEquiv.trans
      (((Algebra.TensorProduct.cancelBaseChange A B C C
        p.asIdeal.ResidueField).symm).toRingEquiv.trans
        ((Algebra.TensorProduct.congr (AlgEquiv.refl : C ≃ₐ[C] C) E).toRingEquiv.trans
          (Algebra.TensorProduct.piRight B C C
            (fun r : F ↦ r.1.asIdeal.ResidueField)).toRingEquiv))
  have hT (x : p.asIdeal.ResidueField) (y : C) :
      T (x ⊗ₜ[A] y) q₀ = y ⊗ₜ[B]
        (Ideal.ResidueField.mapₐ p.asIdeal q (Algebra.ofId A B) rfl x) := by
    simp [T, E, e₀, ψ]
    rfl
  let Q := Algebra.TensorProduct.comm B C q.ResidueField
  have hcoord (z : p.asIdeal.Fiber C) : Q (T z q₀) = φ z := by
    induction z using TensorProduct.inductionOn with
    | tmul x y => exact (congrArg Q (hT x y)).trans (hφ x y).symm
    | add x y hx hy => simp [map_add, hx, hy]
  exact fiber_projection_of_product_equiv q₀ T Q.toRingEquiv φ hcoord

end RingTheory
