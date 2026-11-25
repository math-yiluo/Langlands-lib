/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup.HopfIdeal

/-!
# Regular homomorphisms between matrix groups

A homomorphism `R : S →* GL m k` defined on a subgroup `S` of `GL n k` is *regular* when every
regular function on `GL_m` pulls back along `R` to the restriction to `S` of a regular function on
`GL_n`: its matrix entries and the inverse of its determinant are given on `S` by polynomials in
the entries of the matrix and the inverse of its determinant. Regular homomorphisms map Zariski
closures into Zariski closures.

The determinant `GL n k → GL 1 k` is regular.

## Main definitions

- `Matrix.GeneralLinearGroup.IsRegularOn`: regularity of a homomorphism on a subgroup.
- `Matrix.GeneralLinearGroup.detGL`: the determinant, as a homomorphism `GL n R →* GL (Fin 1) R`.

## Main results

- `Matrix.GeneralLinearGroup.IsRegularOn.mem_zeroLocus_vanishingIdeal`: a regular homomorphism
  maps the Zariski closure of a subgroup into the Zariski closure of its image.
- `Matrix.GeneralLinearGroup.isRegularOn_top`: a homomorphism `GL n k →* GL m k` given by
  polynomials is regular.
- `Matrix.GeneralLinearGroup.exists_algHom_comp_eq_evalAlgHom_detGL`: the determinant is given
  by polynomials.

## Blueprint

- `proposition-central-element-arithmetic-monodromy-group--2`: the regularity of the
  induced actions, and the closure argument.
- `definition-determinant-weight--1`: the determinant.
-/

@[expose] public section

namespace Matrix.GeneralLinearGroup

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] {k : Type*}
  [Field k]

/-- A homomorphism `R : S →* GL m k` on a subgroup `S ≤ GL n k` is *regular* if every regular
function `f` on `GL_m` pulls back to the restriction to `S` of a regular function on `GL_n`.
(blueprint: `proposition-central-element-arithmetic-monodromy-group--2`) -/
def IsRegularOn (S : Subgroup (GL n k)) (R : S →* GL m k) : Prop :=
  ∀ f : CoordinateRing m k, ∃ F : CoordinateRing n k,
    ∀ s : S, evalAlgHom (R s) f = evalAlgHom (s : GL n k) F

/-- A regular homomorphism maps the Zariski closure of a subgroup `Γ ≤ S` into the Zariski
closure of any subgroup containing the image of `Γ`. -/
theorem IsRegularOn.mem_zeroLocus_vanishingIdeal {S : Subgroup (GL n k)} {R : S →* GL m k}
    (hR : IsRegularOn S R) {Γ : Set (GL n k)} (hΓS : Γ ⊆ S) {Γ' : Set (GL m k)}
    (hΓ : ∀ h (hh : h ∈ Γ), R ⟨h, hΓS hh⟩ ∈ Γ') (g : S)
    (hg : (g : GL n k) ∈ {x : GL n k | ∀ a ∈ vanishingIdeal Γ, evalAlgHom x a = 0}) :
    ∀ a ∈ vanishingIdeal Γ', evalAlgHom (R g) a = 0 := by
  intro f hf
  obtain ⟨F, hF⟩ := hR f
  rw [hF]
  refine hg F (mem_vanishingIdeal.2 fun h hh ↦ ?_)
  rw [← hF ⟨h, hΓS hh⟩]
  exact mem_vanishingIdeal.1 hf _ (hΓ h hh)

/-- A homomorphism `GL n k →* GL m k` given by polynomials is regular. -/
theorem isRegularOn_top (r : GL n k →* GL m k) (φ : CoordinateRing m k →ₐ[k] CoordinateRing n k)
    (hφ : ∀ g : GL n k, (evalAlgHom g).comp φ = evalAlgHom (r g)) :
    IsRegularOn ⊤ (r.comp (⊤ : Subgroup (GL n k)).subtype) :=
  fun f ↦ ⟨φ f, fun s ↦ by rw [MonoidHom.comp_apply, ← hφ]; rfl⟩

/-- A homomorphism `GL n k →* GL m k` given by polynomials is regular on every subgroup. -/
theorem IsRegularOn.of_le {S T : Subgroup (GL n k)} (h : S ≤ T) {R : T →* GL m k}
    (hR : IsRegularOn T R) : IsRegularOn S (R.comp (Subgroup.inclusion h)) :=
  fun f ↦ (hR f).imp fun _ hF s ↦ hF (Subgroup.inclusion h s)

/-! ### The determinant -/

variable (n) in
/-- The determinant `GL n R →* GL 1 R`, `g ↦ (det g)`. (blueprint:
`definition-determinant-weight--1`) -/
noncomputable def detGL (R : Type*) [CommRing R] : GL n R →* GL (Fin 1) R :=
  (scalar (Fin 1)).comp det

theorem coe_detGL_apply {R : Type*} [CommRing R] (g : GL n R) (i j : Fin 1) :
    (detGL n R g : Matrix (Fin 1) (Fin 1) R) i j = (g : Matrix n n R).det := by
  simp [detGL, Subsingleton.elim i j]

theorem map_detGL {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (g : GL n R) :
    map f (detGL n R g) = detGL n S (map f g) :=
  Units.ext (Matrix.ext fun i j ↦ by
    change f ((detGL n R g : Matrix (Fin 1) (Fin 1) R) i j) = _
    rw [coe_detGL_apply, coe_detGL_apply]
    exact RingHom.map_det f _)

/-- The determinant is given by polynomials: evaluation at `det g` is evaluation at `g` composed
with an algebra map of coordinate rings. (blueprint: `definition-determinant-weight--1`) -/
theorem exists_algHom_comp_eq_evalAlgHom_detGL :
    ∃ φ : CoordinateRing (Fin 1) k →ₐ[k] CoordinateRing n k,
      ∀ g : GL n k, (evalAlgHom g).comp φ = evalAlgHom (detGL n k g) := by
  refine ⟨evalAlgHom (detGL n _ (genericUnit n k)), fun g ↦ ?_⟩
  rw [← evalAlgHom_map, map_detGL, map_evalAlgHom_genericUnit]

end Matrix.GeneralLinearGroup
