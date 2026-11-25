/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.KummerCover
public import WeilConjectures.CategoryTheory.Sites.EquivariantEvaluation
public import WeilConjectures.FieldTheory.KummerFreeSubgroup
public import WeilConjectures.SixFunctors.ProEtale.KummerCover
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections

/-!
# Galois actions on the geometric generic point with free orbits

Let `X` be an integral scheme with function field `K`, `T = Spec Kˢᵉᵖ` its geometric generic
point in `X_proét`, and `φ : H →* Gal(Kˢᵉᵖ/K)` a group homomorphism. Then `H` acts on `T` on the
right (`AlgebraicGeometry.Scheme.ProEt.genericPointSepAction`), so that pro-étale sheaves can be
evaluated equivariantly at `T` (`CategoryTheory.Sheaf.evaluationRep`).

If `X` is covered by Kummer covers of units `f i` such that `φ x` fixes all `r`-power roots of
some `f i` only for `x = 1`, then `H` acts freely on `Hom(T, W)` for every `W` over a Kummer cover
(`AlgebraicGeometry.Scheme.ProEt.exists_mem_topology_forall_eq_one`). For an abelian variety of
positive dimension over an algebraically closed field, such a cover and a free abelian group `H`
of countable rank exist
(`AlgebraicGeometry.IsAbelianVariety.exists_genericPointSepAction_forall_eq_one`).

## Main definitions

- `AlgebraicGeometry.Scheme.ProEt.genericPointSepAction`: the right action of `H` on `T`.
- `AlgebraicGeometry.ProEtale.constantSheafCompUpperStarIso`: the pullback of a constant sheaf
  is constant.

## Main statements

- `AlgebraicGeometry.Scheme.ProEt.exists_mem_topology_forall_eq_one`.
- `AlgebraicGeometry.IsAbelianVariety.exists_genericPointSepAction_forall_eq_one`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace Scheme.ProEt

variable (X : Scheme.{u}) [IsIntegral X]

/-- The right action of a group `H` on the geometric generic point `T = Spec Kˢᵉᵖ` of `X`
through a homomorphism `φ : H →* Gal(Kˢᵉᵖ/K)`, as a homomorphism `H →* (End T)ᵐᵒᵖ`. -/
noncomputable def genericPointSepAction {H : Type*} [Group H]
    (φ : H →* (SeparableClosure X.functionField ≃ₐ[X.functionField]
      SeparableClosure X.functionField)) :
    H →* (End (genericPointSep X))ᵐᵒᵖ where
  toFun h := MulOpposite.op (End.of (genericPointSepAut X (φ h)))
  map_one' := by
    rw [map_one, genericPointSepAut_one]
    rfl
  map_mul' g h := by
    rw [map_mul, genericPointSepAut_mul]
    rfl

@[simp]
lemma unop_genericPointSepAction {H : Type*} [Group H]
    (φ : H →* (SeparableClosure X.functionField ≃ₐ[X.functionField]
      SeparableClosure X.functionField)) (h : H) :
    (genericPointSepAction X φ h).unop.asHom = genericPointSepAut X (φ h) :=
  rfl

variable {X} in
/-- Let `U i` be a finite affine open cover of an integral scheme `X` with units `f i`, `r` be
invertible on `X` with the `rᵐ`-th roots of unity in the function field `K`, and
`φ : H →* Gal(Kˢᵉᵖ/K)` be such that `φ x` fixes all `r`-power roots of some `f i` only for
`x = 1`. Then every `W` in `X_proét` has a covering sieve (the objects over the Kummer covers of
the `f i`) on whose members `W'` the group `H` acts freely on `Hom(T, W')`. -/
theorem exists_mem_topology_forall_eq_one {ι : Type*} {U : ι → X.Opens} [∀ i, Nonempty (U i)]
    (hU : ∀ i, IsAffineOpen (U i)) (f : ∀ i, Γ(X, U i)) (hf : ∀ i, IsUnit (f i)) {r : ℕ}
    (hr : ∀ i, IsUnit (r : Γ(X, U i))) (hcov : ⨆ i, U i = ⊤)
    (hζ : ∀ m : ℕ, ∃ ζ : X.functionField, IsPrimitiveRoot ζ (r ^ m)) {H : Type*} [Group H]
    (φ : H →* (SeparableClosure X.functionField ≃ₐ[X.functionField]
      SeparableClosure X.functionField))
    (hφ : ∀ i x, (∀ (m : ℕ) (β : SeparableClosure X.functionField),
      β ^ (r ^ m) = algebraMap X.functionField _ (X.germToFunctionField (U i) (f i)) →
        φ x β = β) → x = 1)
    (W : X.ProEt) :
    ∃ S ∈ topology X W, ∀ ⦃W' : X.ProEt⦄ (g : W' ⟶ W), S g →
      ∀ (h : H) (t : genericPointSep X ⟶ W'),
        (genericPointSepAction X φ h).unop.asHom ≫ t = t → h = 1 := by
  refine ⟨(Sieve.ofArrows _ fun i ↦ (isTerminalMkId X).from
      (kummerCover (hU i) (f i) r (hf i) (hr i))).pullback ((isTerminalMkId X).from W),
    (topology X).pullback_stable _ (ofArrows_kummerCover_mem_topology hU f r hf hr hcov), ?_⟩
  rintro W' g ⟨Y, g', k', ⟨i⟩, -⟩ h t ht
  exact hφ i h fun m β hβ ↦
    genericPointSepAut_apply_eq_of_comp_kummerCover (hU i) (hf i) (hr i) hζ t g' (φ h) ht m β hβ

end Scheme.ProEt

/-- Blueprint `sk-rem-sf-fullcd-scope`: let `E` be an abelian variety of positive dimension over
an algebraically closed field `k`, with function field `K`. There is a homomorphism `φ` from a
free abelian group `H` of countable rank to `Gal(Kˢᵉᵖ/K)` such that every object of `E_proét`
has a covering sieve on whose members `W` the group `H` acts freely on `Hom(T, W)`, for the
geometric generic point `T`.

Choose a prime `r` invertible in `k` and a finite affine open cover of `E` by opens `U i` with
units `f i` which are not `r`-th powers in `K`
(`AlgebraicGeometry.IsAbelianVariety.exists_finite_cover_units_not_pow`); `K ⊇ k` contains the
`rᵐ`-th roots of unity, so `exists_injective_kummer_free` provides `φ`, and
`AlgebraicGeometry.Scheme.ProEt.exists_mem_topology_forall_eq_one` the covering sieves. -/
theorem IsAbelianVariety.exists_genericPointSepAction_forall_eq_one {k : Type u} [Field k]
    [IsAlgClosed k] (E : Over (Spec (.of k))) [IsAbelianVariety E]
    (hE : 0 < IsAbelianVariety.dim E) :
    ∃ φ : Multiplicative (ULift.{u + 1} ℕ →₀ ℤ) →*
        (SeparableClosure E.left.functionField ≃ₐ[E.left.functionField]
          SeparableClosure E.left.functionField),
      ∀ W : E.left.ProEt, ∃ S ∈ Scheme.ProEt.topology E.left W, ∀ ⦃W' : E.left.ProEt⦄
        (g : W' ⟶ W), S g → ∀ (h : Multiplicative (ULift.{u + 1} ℕ →₀ ℤ))
          (t : Scheme.ProEt.genericPointSep E.left ⟶ W'),
          (Scheme.ProEt.genericPointSepAction E.left φ h).unop.asHom ≫ t = t → h = 1 := by
  -- a prime `r` invertible in `k`
  obtain ⟨r, hr₁, hr⟩ := Nat.exists_infinite_primes (ringChar k + 1)
  have hrk : (r : k) ≠ 0 := by
    rw [ne_eq, CharP.cast_eq_zero_iff k (ringChar k)]
    intro hdvd
    rcases (Nat.dvd_prime hr).1 hdvd with h | h
    · exact CharP.ringChar_ne_one h
    · omega
  have : NeZero (r : k) := ⟨hrk⟩
  -- the maps `k → Γ(E, V)` and `k → K`
  have : Nonempty (⊤ : E.left.Opens) := ⟨⟨Classical.arbitrary E.left, trivial⟩⟩
  let ψ (V : E.left.Opens) : k →+* Γ(E.left, V) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ E.hom.appTop ≫
      E.left.presheaf.map (homOfLE le_top).op).hom
  let ψK : k →+* E.left.functionField :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ E.hom.appTop ≫ E.left.germToFunctionField ⊤).hom
  have hrK : (r : E.left.functionField) ≠ 0 := by
    rw [← map_natCast ψK]
    exact (map_ne_zero ψK).2 hrk
  have hζ (m : ℕ) : ∃ ζ : E.left.functionField, IsPrimitiveRoot ζ (r ^ m) := by
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot k (r ^ m)
    exact ⟨ψK ζ, hζ.map_of_injective ψK.injective⟩
  obtain ⟨ι, _, U, _, f, hU, hf, hcov, hpow⟩ :=
    IsAbelianVariety.exists_finite_cover_units_not_pow E hE hr.two_le
  have hrU (i : ι) : IsUnit (r : Γ(E.left, U i)) := by
    rw [← map_natCast (ψ (U i))]
    exact (Ne.isUnit hrk).map (ψ (U i))
  obtain ⟨φ, hφ⟩ := exists_injective_kummer_free hr hrK hζ
    (fun i ↦ E.left.germToFunctionField (U i) (f i))
    (fun i ↦ ((hf i).map (E.left.germToFunctionField (U i)).hom).ne_zero) hpow
  exact ⟨φ, Scheme.ProEt.exists_mem_topology_forall_eq_one hU f hf hrU hcov hζ φ hφ⟩

namespace ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {Z W : Scheme.{u}}

/-- The pullback of a constant pro-étale sheaf is constant: `g^*` composed with the constant
sheaf functor and the constant sheaf functor are both left adjoint to the global sections
functor, as `Γ(W, g_* -) ≅ Γ(Z, -)`
(`AlgebraicGeometry.ProEtale.globalSectionsLowerStarIso`). -/
noncomputable def constantSheafCompUpperStarIso (g : Z ⟶ W) :
    constantSheaf (Scheme.ProEt.topology W) A ⋙ (g)^*[A] ≅
      constantSheaf (Scheme.ProEt.topology Z) A :=
  (((constantSheafΓAdj _ A).comp (upperStarLowerStarAdjunction A g)).ofNatIsoRight
    (globalSectionsLowerStarIso A g)).leftAdjointUniq (constantSheafΓAdj _ A)

end ProEtale

end AlgebraicGeometry
