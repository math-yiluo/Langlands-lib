/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.ProEtale.IndBijectiveOnStalks
public import WeilConjectures.RingTheory.ProEtale.LocalIso

/-!
# Algebras realizing the pullback of `Spec R` along a profinite map

In this file we prove a variant of Stacks 097F: let `R → S` be a w-local map of w-local rings
which is bijective on stalks, and let `P` be any `R`-algebra which is bijective on stalks over
`R` and whose spectrum realizes the topological pullback
`Spec R ×_{π₀(Spec R)} π₀(Spec S)`. Then `P ≃ₐ[R] S`.

The proof is the same as the one of `Algebra.BijectiveOnStalks.indZariski_of_isWLocal`, where
the ring `PullbackProfinite R T i` is replaced by `P`.

## Main results

- `Algebra.BijectiveOnStalks.nonempty_algEquiv_of_isPullback`: the variant of Stacks 097F.
-/

@[expose] public section

universe u

open CategoryTheory TopCat PrimeSpectrum

variable {R S P : Type u} [CommRing R] [CommRing S] [CommRing P]

/-- The continuous map `π₀(Spec S) → π₀(Spec R)` induced by a ring map `f : R →+* S`. -/
noncomputable def PrimeSpectrum.connectedComponentsComap (f : R →+* S) :
    C(ConnectedComponents (PrimeSpectrum S), ConnectedComponents (PrimeSpectrum R)) :=
  ⟨(PrimeSpectrum.continuous_comap f).connectedComponentsMap,
    (PrimeSpectrum.continuous_comap f).connectedComponentsMap_continuous⟩

@[simp]
lemma PrimeSpectrum.connectedComponentsComap_mk (f : R →+* S) (x : PrimeSpectrum S) :
    connectedComponentsComap f (ConnectedComponents.mk x) =
      ConnectedComponents.mk (PrimeSpectrum.comap f x) :=
  (PrimeSpectrum.continuous_comap f).connectedComponentsMap_mk x

variable (R S P) in
/-- **Variant of Stacks 097F**: let `R → S` be a w-local map of w-local rings that is
bijective on stalks, and let `P` be an `R`-algebra that is bijective on stalks over `R` such
that the square
```
Spec P --p--→ π₀(Spec S)
  |              |
  ↓              ↓
Spec R ------→ π₀(Spec R)
```
is cartesian in the category of topological spaces. Then `P` and `S` are isomorphic as
`R`-algebras. -/
theorem Algebra.BijectiveOnStalks.nonempty_algEquiv_of_isPullback [Algebra R S] [Algebra R P]
    [IsWLocalRing R] [IsWLocalRing S] [Algebra.BijectiveOnStalks R S]
    [Algebra.BijectiveOnStalks R P] (hw : (algebraMap R S).IsWLocal)
    (p : C(PrimeSpectrum P, ConnectedComponents (PrimeSpectrum S)))
    (pb : IsPullback (ofHom p) (ofHom ⟨PrimeSpectrum.comap (algebraMap R P),
        PrimeSpectrum.continuous_comap _⟩)
      (ofHom (connectedComponentsComap (algebraMap R S)))
      (ofHom ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩)) :
    Nonempty (P ≃ₐ[R] S) := by
  set T := ConnectedComponents (PrimeSpectrum S)
  -- The canonical map `Spec S → Spec P` over `Spec R` via the pullback property.
  let a : TopCat.of (PrimeSpectrum S) ⟶ TopCat.of T :=
    ofHom ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩
  let b : TopCat.of (PrimeSpectrum S) ⟶ TopCat.of (PrimeSpectrum R) :=
    ofHom ⟨PrimeSpectrum.comap (algebraMap R S), PrimeSpectrum.continuous_comap _⟩
  have w : a ≫ ofHom (connectedComponentsComap (algebraMap R S)) =
      b ≫ ofHom ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩ := by
    ext y
    exact connectedComponentsComap_mk (algebraMap R S) y
  let φ : TopCat.of (PrimeSpectrum S) ⟶ TopCat.of (PrimeSpectrum P) := pb.lift a b w
  have hφT (y : PrimeSpectrum S) : p (φ y) = ConnectedComponents.mk y :=
    ConcreteCategory.congr_hom (pb.lift_fst a b w) y
  have hφR (y : PrimeSpectrum S) : PrimeSpectrum.comap (algebraMap R P) (φ y) =
      PrimeSpectrum.comap (algebraMap R S) y :=
    ConcreteCategory.congr_hom (pb.lift_snd a b w) y
  let Φ : Algebra.BijectiveOnStalks.HomOver R P S :=
    { toContinuousMap := φ.hom
      comp_comap_algebraMap := fun y ↦ hφR y }
  -- By fully faithfulness (Stacks 096L), `Φ` comes from an `R`-algebra map `g : P → S`.
  let g : P →ₐ[R] S := Algebra.BijectiveOnStalks.algHom_of_continuousMap R P S Φ
  have hg (y : PrimeSpectrum S) : PrimeSpectrum.comap g.toRingHom y = φ y :=
    DFunLike.congr_fun
      (Algebra.BijectiveOnStalks.continuousMap_of_algHom_algHom_of_continuousMap R P S Φ) y
  -- `Spec P` is w-local.
  have : IsWLocalRing P := ⟨ConnectedComponents.wlocalSpace_of_isPullback pb⟩
  -- `g` is a w-local map.
  have hgw : RingHom.IsWLocal g.toRingHom := by
    refine ⟨PrimeSpectrum.isSpectralMap_comap _, fun n hn ↦ ?_⟩
    rw [Set.mem_preimage, hg n,
      ← ConnectedComponents.preimage_closedPoints_eq_closedPoints_of_isPullback pb,
      Set.mem_preimage]
    rw [ContinuousMap.coe_mk, hφR n]
    exact hw.closedPoints_subset_preimage_closedPoints hn
  -- `g` identifies local rings.
  have hgs : g.toRingHom.BijectiveOnStalks := by
    have h1 : (algebraMap R P).BijectiveOnStalks :=
      RingHom.bijectiveOnStalks_algebraMap.mpr inferInstance
    have h2 : (g.toRingHom.comp (algebraMap R P)).BijectiveOnStalks := by
      have heq : g.toRingHom.comp (algebraMap R P) = algebraMap R S :=
        RingHom.ext fun x ↦ g.commutes x
      rw [heq]
      exact RingHom.bijectiveOnStalks_algebraMap.mpr inferInstance
    exact RingHom.BijectiveOnStalks.of_comp h1 h2
  -- `g` is bijective on connected components.
  have hb : (PrimeSpectrum.continuous_comap g.toRingHom).connectedComponentsMap.Bijective := by
    have hL := ConnectedComponents.lift_bijective_of_isPullback pb
    set L := Continuous.connectedComponentsLift p.2 with hLdef
    have hkey (c : ConnectedComponents (PrimeSpectrum S)) :
        L ((PrimeSpectrum.continuous_comap g.toRingHom).connectedComponentsMap c) = c := by
      obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe c
      rw [Continuous.connectedComponentsMap_mk, hg y]
      exact hφT y
    refine ⟨fun c₁ c₂ h12 ↦ ?_, fun d ↦ ⟨L d, hL.injective (hkey (L d))⟩⟩
    rw [← hkey c₁, h12, hkey c₂]
  exact ⟨AlgEquiv.ofBijective g (RingHom.IsWLocal.bijective_of_bijective hgw hgs hb)⟩
