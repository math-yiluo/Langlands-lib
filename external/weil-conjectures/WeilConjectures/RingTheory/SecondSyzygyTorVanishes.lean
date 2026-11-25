/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.Algebra.Category.ModuleCat.TorSymmetry
import WeilConjectures.Algebra.TorDimensionShifting
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.KoszulResolution

/-!
# Vanishing of first Tor for second syzygies over two variables

Source: blueprint `theorem-riemann-roch-coherent-serre-duality`, Koszul resolution and dimension
shifting.
-/

@[expose] public section

universe u v

open CategoryTheory

namespace MvPolynomial

/-- Source: blueprint `theorem-riemann-roch-coherent-serre-duality`, the Koszul resolution of the
constant-coefficient module. Its kernel is the variable ideal, as seen from the support
criterion for the first power of `idealOfVars`. Restrict the Koszul middle map to this
kernel. The resulting two short exact sequences have free middle terms and first term
`S`. Dimension shifting identifies `Tor₃(k,N)` with `Tor₁(S,N)`, which vanishes because
`S` is projective. -/
private theorem third_tor_constantCoeff {k : Type u} [Field k]
    (N : ModuleCat.{u} (MvPolynomial (Fin 2) k)) :
    CategoryTheory.Limits.IsZero (((Tor' (ModuleCat.{u} (MvPolynomial (Fin 2) k)) 3).obj
      ((ModuleCat.restrictScalars
        (constantCoeff : MvPolynomial (Fin 2) k →+* k)).obj (ModuleCat.of k k))).obj N) := by
  classical
  let S := MvPolynomial (Fin 2) k
  let K : ModuleCat.{u} S :=
    (ModuleCat.restrictScalars (constantCoeff : S →+* k)).obj (ModuleCat.of k k)
  let c : S →ₗ[S] K :=
    { toFun := constantCoeff
      map_add' := constantCoeff.map_add
      map_smul' := fun a b ↦ constantCoeff.map_mul a b }
  have hc : Function.Surjective c := fun x ↦ ⟨C x, by simp [c]⟩
  obtain ⟨f, g, q, _, _, _, hinj, hfg, hgq, _, hker, _, _⟩ :=
    AlgebraicGeometry.ProjectiveLine.koszul_resolution (k := k)
  have hrange : Set.range (X : Fin 2 → S) = ({X 0, X 1} : Set S) := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hcz (a : S) : c a = 0 ↔ q a = 0 := by
    rw [hker, ← hrange]
    change constantCoeff a = 0 ↔ a ∈ idealOfVars (Fin 2) k
    rw [← pow_one (idealOfVars (Fin 2) k), mem_pow_idealOfVars_iff']
    simp [constantCoeff_eq, Finsupp.degree_eq_zero_iff]
  have hgc : Function.Exact g c := fun a ↦ (hcz a).trans (hgq a)
  let g' : S × S →ₗ[S] c.ker :=
    g.codRestrict c.ker (fun p ↦ (hgc (g p)).mpr ⟨p, rfl⟩)
  have hg' : Function.Surjective g' := by
    intro x
    obtain ⟨p, hp⟩ := (hgc x.val).mp x.property
    exact ⟨p, Subtype.ext hp⟩
  have hfg' : Function.Exact f g' := by
    intro p
    rw [← hfg p]
    exact ⟨fun h ↦ congrArg Subtype.val h, fun h ↦ Subtype.ext h⟩
  let E := ModuleCat.shortComplexOfCompEqZero f g' hfg'.linearMap_comp_eq_zero
  have hE : E.ShortExact := ModuleCat.shortComplex_shortExact E hfg' hinj hg'
  obtain ⟨⟨θ, _⟩, _⟩ := tor_dimension_shifting N c.shortComplexKer E
    (LinearMap.shortExact_shortComplexKer hc) hE rfl
  exact CategoryTheory.Limits.IsZero.of_iso
    (isZero_Tor'_succ_of_projective (ModuleCat.{u} S) (ModuleCat.of S S) N 0)
    (θ N).symm

/-- The second kernel of two finite free surjections has vanishing first Tor with `k`.
Source: blueprint `theorem-riemann-roch-coherent-serre-duality`, proof, Koszul resolution and
dimension shifting (blueprint: lem-sc-p1-second-syzygy-tor-vanishes).

Proof: the two surjections give short exact sequences
`0 → ker q₀ → F₀ → M → 0` and `0 → ker q₁ → F₁ → ker q₀ → 0`.
If the universe of `M` differs from the ring universe, replace it by the small quotient
`F₀ / ker q₀` using the first isomorphism theorem; this leaves both kernels unchanged.
The displayed finite bases make both middle terms free. Apply the first, natural-isomorphism
clause of `tor_dimension_shifting` to identify `Tor₁(ker q₁,k)` with `Tor₃(M,k)`.
Use `nonempty_tor'_flip_iso` to identify the latter with `Tor₃(k,M)`. The explicit exact
Koszul complex `koszul_resolution` resolves `S/(X 0,X 1)` by the free modules `S`, `S²`, `S`.
Its last quotient is canonically the restriction of scalars of `k` along `constantCoeff`:
the kernel of constant coefficient is precisely `(X 0,X 1)`, as every nonconstant monomial
is divisible by a variable. Package this complex as a projective resolution and compute Tor
by tensoring it with `M`. The complex is zero in degree three, so its third homology is zero.
Transport this zero object across symmetry and dimension shifting and use the equivalence
between zero module objects and subsingleton carriers. No grading assumption is needed for
this vanishing. The argument also applies when either free module has rank zero. -/
theorem second_syzygy_tor_vanishes {k : Type u} [Field k]
    {M : Type v} [AddCommGroup M] [Module (MvPolynomial (Fin 2) k) M]
    (F₀ F₁ : ModuleCat.{u} (MvPolynomial (Fin 2) k))
    (r₀ r₁ : ℕ)
    (b₀ : Module.Basis (Fin r₀) (MvPolynomial (Fin 2) k) F₀)
    (b₁ : Module.Basis (Fin r₁) (MvPolynomial (Fin 2) k) F₁)
    (q₀ : F₀ →ₗ[MvPolynomial (Fin 2) k] M) (hq₀ : Function.Surjective q₀)
    (q₁ : F₁ →ₗ[MvPolynomial (Fin 2) k] q₀.ker) (hq₁ : Function.Surjective q₁) :
    Subsingleton (((Tor' (ModuleCat.{u} (MvPolynomial (Fin 2) k)) 1).obj
      (ModuleCat.of (MvPolynomial (Fin 2) k) q₁.ker)).obj
      ((ModuleCat.restrictScalars
        (MvPolynomial.constantCoeff : MvPolynomial (Fin 2) k →+* k)).obj
        (ModuleCat.of k k))) := by
  -- Surjectivity identifies this small quotient with M; Tor only needs the quotient.
  have _eM := q₀.quotKerEquivOfSurjective hq₀
  let S := MvPolynomial (Fin 2) k
  let K : ModuleCat.{u} S :=
    (ModuleCat.restrictScalars (constantCoeff : S →+* k)).obj (ModuleCat.of k k)
  let p : F₀ →ₗ[S] F₀ ⧸ q₀.ker := q₀.ker.mkQ
  have hpker : p.ker = q₀.ker := Submodule.ker_mkQ _
  let e : q₀.ker ≃ₗ[S] p.ker := LinearEquiv.ofEq _ _ hpker.symm
  let q : F₁ →ₗ[S] p.ker := e.toLinearMap.comp q₁
  have hq : Function.Surjective q := e.surjective.comp hq₁
  have hqker : q.ker = q₁.ker := by
    ext x
    simp [q, LinearMap.mem_ker]
  let eker : ModuleCat.of S q₁.ker ≅ ModuleCat.of S q.ker :=
    (LinearEquiv.ofEq _ _ hqker.symm).toModuleIso
  let : Module.Free S F₀ := Module.Free.of_basis b₀
  let : Module.Free S F₁ := Module.Free.of_basis b₁
  obtain ⟨⟨θ, _⟩, _⟩ := tor_dimension_shifting K p.shortComplexKer q.shortComplexKer
    (LinearMap.shortExact_shortComplexKer q₀.ker.mkQ_surjective)
    (LinearMap.shortExact_shortComplexKer hq) rfl
  obtain ⟨σ⟩ := nonempty_tor'_flip_iso S 3
  let esym := (σ.app (ModuleCat.of S (F₀ ⧸ q₀.ker))).app K
  let etor := ((Tor' (ModuleCat.{u} S) 1).mapIso eker).app K
  apply ModuleCat.subsingleton_of_isZero
  exact CategoryTheory.Limits.IsZero.of_iso (third_tor_constantCoeff (ModuleCat.of S (F₀ ⧸ q₀.ker)))
    (etor ≪≫ θ K ≪≫ esym)

end MvPolynomial
