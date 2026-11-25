/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.ProEtale.BijectiveOnStalksPullback
public import WeilConjectures.RingTheory.ProEtale.WeaklyEtaleWStrictlyLocal
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra
public import WeilConjectures.RingTheory.ProEtale.WStrictlyLocalUniversalHomeomorphism

/-!
# Weakly étale algebras over a universal homeomorphism

Let `A → A'` be a universal homeomorphism and let `B` be a weakly étale `A'`-algebra. We show
that, locally for the ind-étale topology on `A`, `B` comes from `A`: there is an ind-étale
`A`-algebra `D` and a faithfully flat `A'`-algebra map `B → A' ⊗[A] D`. We first prove this
assuming that the base change `A' ⊗[A] C` of the w-strict localization
`C = WStrictLocalization A` is w-strictly local, and then discharge this assumption using
`IsWStrictlyLocalRing.of_isUniversalHomeomorphism`.

## Proof

Let `C = WStrictLocalization A` and `C' = A' ⊗[A] C`. Then `Spec C' → Spec C` is a
homeomorphism and the closed points of `Spec C'` map onto `Spec A'`.
1. By `Algebra.WeaklyEtale.exists_bijectiveOnStalks_of_isWStrictlyLocalRing`, there is a
   w-local `C'`-algebra `D` with `C' → D` w-local and bijective on stalks, and a faithfully flat
   ring map `B → D`.
2. Let `T = π₀(Spec D)` with its map `i₀ : T → π₀(Spec C)`, let `Q = PullbackProfinite C T i₀`
   (ind-Zariski over `C`, hence ind-étale over `A`) and `P = C' ⊗[C] Q`. Then `P` is bijective
   on stalks over `C'`, and since `Spec P ≃ Spec Q` and `Spec C' ≃ Spec C`, the spectrum of
   `P` realizes `Spec C' ×_{π₀(Spec C')} T`.
3. By `Algebra.BijectiveOnStalks.nonempty_algEquiv_of_isPullback` we get `P ≃ₐ[C'] D`, and
   `P ≃ₐ[A'] A' ⊗[A] Q` by cancelling base change. The composite `B → D ≃ P ≃ A' ⊗[A] Q` is
   the desired faithfully flat map.

## Main results

- `Algebra.WeaklyEtale.exists_indEtale_baseChange_of_isWStrictlyLocalRing`: the statement
  assuming that `A' ⊗[A] WStrictLocalization A` is w-strictly local.
- `Algebra.WeaklyEtale.exists_indEtale_baseChange`: local descent of weakly étale algebras along
  universal homeomorphisms.
-/

@[expose] public section

universe u

open CategoryTheory TopCat PrimeSpectrum TensorProduct WContractification

namespace Algebra.IsUniversalHomeomorphism

variable {A B B' : Type u} [CommRing A] [CommRing B] [CommRing B'] [Algebra A B] [Algebra A B']

/-- Being a universal homeomorphism is invariant under isomorphisms of algebras. -/
lemma of_algEquiv (e : B ≃ₐ[A] B') [Algebra.IsUniversalHomeomorphism A B] :
    Algebra.IsUniversalHomeomorphism A B' where
  isUniversalHomeomorphism := by
    have h : AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A B')) =
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (e : B →+* B')) ≫
          AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A B)) := by
      rw [← AlgebraicGeometry.Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a
      simp
    rw [h]
    have : IsIso (CommRingCat.ofHom (e : B →+* B')) :=
      (e.toRingEquiv.toCommRingCatIso).isIso_hom
    infer_instance

/-- Universal homeomorphisms of rings are stable under base change, in the form of pushout
squares: if `S' = R' ⊗[R] S` and `R → S` is a universal homeomorphism, so is `R' → S'`. -/
lemma of_isPushout (R S R' S' : Type u) [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R S] [Algebra R R'] [Algebra R S'] [Algebra S S'] [Algebra R' S']
    [IsScalarTower R S S'] [IsScalarTower R R' S'] [Algebra.IsPushout R S R' S']
    [Algebra.IsUniversalHomeomorphism R S] :
    Algebra.IsUniversalHomeomorphism R' S' :=
  have : Algebra.IsPushout R R' S S' := Algebra.IsPushout.symm inferInstance
  of_algEquiv (Algebra.IsPushout.equiv R R' S S')

/-- If `A → B` is a universal homeomorphism, then `Spec B → Spec A` is a homeomorphism. -/
lemma isHomeomorph_comap [Algebra.IsUniversalHomeomorphism A B] :
    IsHomeomorph (PrimeSpectrum.comap (algebraMap A B)) :=
  isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
    ⟨PrimeSpectrum.continuous_comap _,
      PrimeSpectrum.isClosedMap_comap_of_isIntegral _
        ((algebraMap_isIntegral_iff (R := A) (A := B)).mpr inferInstance),
      AlgebraicGeometry.Algebra.IsUniversalHomeomorphism.comap_bijective A B⟩

end Algebra.IsUniversalHomeomorphism

/-- A homeomorphism `X ≃ₜ Y` induces an isomorphism `π₀(X) ≅ π₀(Y)` in `TopCat`. -/
noncomputable def Homeomorph.connectedComponentsIso {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] (h : X ≃ₜ Y) :
    TopCat.of (ConnectedComponents X) ≅ TopCat.of (ConnectedComponents Y) where
  hom := ofHom ⟨h.continuous.connectedComponentsMap, h.continuous.connectedComponentsMap_continuous⟩
  inv := ofHom ⟨h.symm.continuous.connectedComponentsMap,
    h.symm.continuous.connectedComponentsMap_continuous⟩
  hom_inv_id := by
    ext c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    simp [Continuous.connectedComponentsMap_mk]
  inv_hom_id := by
    ext c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    simp [Continuous.connectedComponentsMap_mk]

@[simp]
lemma Homeomorph.connectedComponentsIso_hom_mk {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] (h : X ≃ₜ Y) (x : X) :
    h.connectedComponentsIso.hom (ConnectedComponents.mk x) = ConnectedComponents.mk (h x) :=
  Continuous.connectedComponentsMap_mk h.continuous x

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **Local descent of weakly étale algebras along universal homeomorphisms.** Let `A → A'` be a
universal homeomorphism and `B` a weakly étale `A'`-algebra. Assume that `A' ⊗[A] C` is
w-strictly local, where `C = WStrictLocalization A`. Then there is an ind-étale `A`-algebra `D`
and a faithfully flat `A'`-algebra map `B → A' ⊗[A] D`. -/
theorem Algebra.WeaklyEtale.exists_indEtale_baseChange_of_isWStrictlyLocalRing
    (A A' B : Type u) [CommRing A] [CommRing A'] [CommRing B] [Algebra A A']
    [Algebra.IsUniversalHomeomorphism A A'] [Algebra A' B] [Algebra.WeaklyEtale A' B]
    [IsWStrictlyLocalRing (A' ⊗[A] WStrictLocalization A)] :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra A D), Algebra.IndEtale A D ∧
      ∃ φ : B →ₐ[A'] A' ⊗[A] D, φ.toRingHom.FaithfullyFlat := by
  classical
  set C := WStrictLocalization A
  set C' := A' ⊗[A] C
  -- `Spec C' → Spec C` is a homeomorphism.
  have : Algebra.IsUniversalHomeomorphism C C' :=
    Algebra.IsUniversalHomeomorphism.of_isPushout A A' C C'
  have hhC := Algebra.IsUniversalHomeomorphism.isHomeomorph_comap (A := C) (B := C')
  set hC := hhC.homeomorph _
  -- Every prime of `A'` is the image of a closed point of `Spec C'`.
  have hclosed (p : PrimeSpectrum A') : ∃ x ∈ closedPoints (PrimeSpectrum C'),
      PrimeSpectrum.comap (algebraMap A' C') x = p := by
    obtain ⟨x, hx_mem, hx⟩ :=
      WStrictLocalization.exists_mem_zeroLocus_comap_eq A (comap (algebraMap A A') p)
    rw [WStrictLocalization.zeroLocus_map_eq_closedPoints] at hx_mem
    obtain ⟨x', rfl⟩ := hhC.surjective x
    refine ⟨x', ?_, ?_⟩
    · rw [mem_closedPoints_iff, ← hhC.injective.preimage_image {x'}, Set.image_singleton]
      exact (mem_closedPoints_iff.mp hx_mem).preimage (continuous_comap _)
    · apply AlgebraicGeometry.Algebra.IsUniversalHomeomorphism.comap_injective A A'
      rw [← hx, ← comap_comp_apply, ← comap_comp_apply, ← IsScalarTower.algebraMap_eq A A' C',
        ← IsScalarTower.algebraMap_eq A C C']
  -- Step 1: the w-local `C'`-algebra `D`.
  obtain ⟨D, _, _, f, hDw, hbos, hwloc, hff, hcomm⟩ :=
    Algebra.WeaklyEtale.exists_bijectiveOnStalks_of_isWStrictlyLocalRing A' C' B hclosed
  -- Step 2: the ind-Zariski `C`-algebra `Q` and its base change `P` to `C'`.
  set T := ConnectedComponents (PrimeSpectrum D)
  set gD : C →+* D := (algebraMap C' D).comp (algebraMap C C')
  set i₀ := connectedComponentsComap gD
  set Q := PullbackProfinite C T i₀
  set P := C' ⊗[C] Q
  have : Algebra.IsUniversalHomeomorphism Q P :=
    Algebra.IsUniversalHomeomorphism.of_isPushout C C' Q P
  have hhP := Algebra.IsUniversalHomeomorphism.isHomeomorph_comap (A := Q) (B := P)
  set hP := hhP.homeomorph _
  have : Algebra.IndZariski C' P :=
    (RingHom.IndZariski.algebraMap_iff (R := C') (S := P)).mp
      (RingHom.IndZariski.isStableUnderBaseChange C Q C' P
        ((RingHom.IndZariski.algebraMap_iff (R := C) (S := Q)).mpr inferInstance))
  have hCP : (algebraMap C' P).comp (algebraMap C C') = (algebraMap Q P).comp (algebraMap C Q) :=
    RingHom.ext fun c ↦ Algebra.TensorProduct.tmul_one_eq_one_tmul c
  -- The spectrum of `P` realizes the pullback `Spec C' ×_{π₀(Spec C')} T`.
  let p : C(PrimeSpectrum P, T) :=
    (PullbackProfinite.projT C T i₀).comp ⟨comap (algebraMap Q P), continuous_comap _⟩
  have pb : IsPullback (ofHom p) (ofHom ⟨comap (algebraMap C' P), continuous_comap _⟩)
      (ofHom (connectedComponentsComap (algebraMap C' D)))
      (ofHom ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩) := by
    refine (PullbackProfinite.isPullback C T i₀).of_iso (isoOfHomeo hP.symm) (Iso.refl _)
      (isoOfHomeo hC.symm) hC.symm.connectedComponentsIso ?_ ?_ ?_ ?_
    · refine TopCat.hom_ext (ContinuousMap.ext fun y ↦ ?_)
      simp [p, hP, Function.surjInv_eq]
    · refine TopCat.hom_ext (ContinuousMap.ext fun y ↦ ?_)
      simp only [isoOfHomeo_hom, TopCat.hom_comp, ConcreteCategory.hom_ofHom,
        ContinuousMap.comp_apply, ContinuousMap.coe_mk]
      apply hhC.injective
      have hCs (z : PrimeSpectrum C) : comap (algebraMap C C') (hC.symm z) = z :=
        hC.apply_symm_apply z
      have hPs (z : PrimeSpectrum Q) : comap (algebraMap Q P) (hP.symm z) = z :=
        hP.apply_symm_apply z
      rw [hCs, ← comap_comp_apply, hCP, comap_comp_apply, hPs]
      rfl
    · refine TopCat.hom_ext (ContinuousMap.ext fun t ↦ ?_)
      obtain ⟨d, rfl⟩ := ConnectedComponents.surjective_coe t
      simp only [TopCat.hom_comp, ConcreteCategory.hom_ofHom, ContinuousMap.comp_apply,
        Iso.refl_hom, Category.id_comp]
      rw [connectedComponentsComap_mk, connectedComponentsComap_mk,
        Homeomorph.connectedComponentsIso_hom_mk, comap_comp_apply]
      exact congrArg ConnectedComponents.mk (hC.symm_apply_apply _)
    · refine TopCat.hom_ext (ContinuousMap.ext fun x ↦ ?_)
      exact hC.symm.connectedComponentsIso_hom_mk x
  -- Step 3: `P ≃ₐ[C'] D` and the final map.
  obtain ⟨e⟩ := Algebra.BijectiveOnStalks.nonempty_algEquiv_of_isPullback C' D P hwloc p pb
  let : Algebra A Q := ((algebraMap C Q).comp (algebraMap A C)).toAlgebra
  have : IsScalarTower A C Q := .of_algebraMap_eq' rfl
  have : Algebra.IndEtale A Q := Algebra.IndEtale.trans A (S := C) Q
  let cbc : P ≃ₐ[A'] A' ⊗[A] Q := Algebra.IsPushout.cancelBaseChangeAlg A A' C C' Q
  let φ : B →ₐ[A'] A' ⊗[A] Q :=
    { toRingHom := cbc.toRingHom.comp (e.symm.toRingHom.comp f)
      commutes' := fun a ↦ by
        have h1 := RingHom.congr_fun hcomm a
        simp only [RingHom.comp_apply] at h1
        have h2 : algebraMap C' P (algebraMap A' C' a) = algebraMap A' P a :=
          (IsScalarTower.algebraMap_apply A' C' P a).symm
        simp [h1, h2] }
  refine ⟨Q, inferInstance, inferInstance, inferInstance, φ, ?_⟩
  exact RingHom.FaithfullyFlat.stableUnderComposition _ _
    (RingHom.FaithfullyFlat.stableUnderComposition _ _ hff
      (.of_bijective e.symm.bijective)) (.of_bijective cbc.bijective)

/-- **Local descent of weakly étale algebras along universal homeomorphisms**: if `A → A'` is a
universal homeomorphism and `B` is a weakly étale `A'`-algebra, there are an ind-étale
`A`-algebra `D` and a faithfully flat `A'`-algebra map `B → A' ⊗[A] D`. In other words, every
weakly étale `Spec A'`-scheme is covered, for the pro-étale topology, by the base change of an
ind-étale `Spec A`-scheme. The w-strict localization `A' ⊗[A] WStrictLocalization A` is
w-strictly local by `IsWStrictlyLocalRing.of_isUniversalHomeomorphism`. -/
theorem Algebra.WeaklyEtale.exists_indEtale_baseChange
    (A A' B : Type u) [CommRing A] [CommRing A'] [CommRing B] [Algebra A A']
    [Algebra.IsUniversalHomeomorphism A A'] [Algebra A' B] [Algebra.WeaklyEtale A' B] :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra A D), Algebra.IndEtale A D ∧
      ∃ φ : B →ₐ[A'] A' ⊗[A] D, φ.toRingHom.FaithfullyFlat :=
  letI := Algebra.TensorProduct.rightAlgebra (R := A) (A := A') (B := WStrictLocalization A)
  have : Algebra.IsUniversalHomeomorphism (WStrictLocalization A)
      (A' ⊗[A] WStrictLocalization A) :=
    Algebra.IsUniversalHomeomorphism.of_isPushout A A' _ _
  have : IsWStrictlyLocalRing (A' ⊗[A] WStrictLocalization A) :=
    IsWStrictlyLocalRing.of_isUniversalHomeomorphism (WStrictLocalization A) _
  exists_indEtale_baseChange_of_isWStrictlyLocalRing A A' B
