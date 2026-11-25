/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LatticeSections

/-!
# Semilinearity of lattice maps for locally constant natural numbers

Let `F` be a sheaf of `ℚ̄_ℓ,X`-modules and `ψ_U : C(U, M) → F(U)` additive maps, natural in `U`.
Sections of `F` over `U` are determined by their restrictions to an open cover of `U`
(`AlgebraicGeometry.ProEtale.AdicSheaf.sections_ext_of_opens`). Hence `ψ(g • m) = ι(g) • ψ(m)`
for every function `g` which is locally constant with values in `ℕ`
(`AlgebraicGeometry.ProEtale.AdicSheaf.map_smul_of_locally_natCast`): on an open where `g` is
the constant `n`, both sides are `n • ψ(m)`.
-/

@[expose] public section
universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale.AdicSheaf

open PadicAlgCl

variable {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}

/-- Sections of an `ℓ`-adic sheaf over `U` are determined by their restrictions to the members
of an open cover of `U`. -/
lemma sections_ext_of_opens (F : AdicSheaf l X) {U : X.ProEt} {ι : Type u} (O : ι → U.left.Opens)
    (hO : ∀ x, ∃ i, x ∈ O i) {s t : F.X.obj.obj (op U)}
    (h : ∀ i, F.X.obj.map (Scheme.ProEt.ofOpenImmersionHom U (O i).ι).op s =
      F.X.obj.map (Scheme.ProEt.ofOpenImmersionHom U (O i).ι).op t) : s = t := by
  have hS := Scheme.ProEt.mem_topology_of_openImmersion
    (Sieve.ofArrows _ fun i ↦ Scheme.ProEt.ofOpenImmersionHom U (O i).ι) (fun i ↦ (O i).ι)
    (fun x ↦ (hO x).elim fun i hi ↦ ⟨i, by simpa using hi⟩)
    (fun i ↦ Sieve.ofArrows_mk _ _ i)
  have hP := (isSheaf_iff_isSheaf_of_type _ _).mp
    ((Presheaf.isSheaf_iff_isSheaf_forget _ F.X.obj
      (CategoryTheory.forget (WeilCoefficients.{u} l))).mp F.X.property)
  refine (hP _ hS).isSeparatedFor.ext fun V f hf ↦ ?_
  obtain ⟨W, a, _, ⟨i⟩, rfl⟩ := hf
  change F.X.obj.map (a ≫ _).op s = F.X.obj.map (a ≫ _).op t
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, h i]

variable {R : Type} [CommRing R] [TopologicalSpace R] (ι : R →+* PadicAlgCl l) (hι : Continuous ι)
  {E : IntermediateField ℚ_[l] (PadicAlgCl l)} [FiniteDimensional ℚ_[l] E] (hιE : ∀ x, ι x ∈ E)
  (F : AdicSheaf l X) {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousSMul R M]
  (ψ : ∀ U : X.ProEt, C(U.left, M) →+ F.X.obj.obj (op U))
  (hψ : ∀ ⦃U V : X.ProEt⦄ (f : V ⟶ U) (m : C(U.left, M)),
    ψ V (m.comp f.left.base.hom) = F.X.obj.map f.op (ψ U m))

include hψ in
/-- **Semilinearity for locally constant natural numbers**: natural additive maps
`ψ_U : C(U, M) → F(U)` satisfy `ψ(g • m) = ι(g) • ψ(m)` for every function `g` which is locally
constant with values in `ℕ`. -/
lemma map_smul_of_locally_natCast {U : X.ProEt} (g : C(U.left, R))
    (hg : ∀ x, ∃ O : U.left.Opens, x ∈ O ∧ ∃ n : ℕ, ∀ y ∈ O, g y = n) (m : C(U.left, M)) :
    ψ U (g • m) = sectionAct F (ULift.up (ringValuedFunction ι hι hιE g)) (ψ U m) := by
  choose O hxO n hn using hg
  refine sections_ext_of_opens F O (fun x ↦ ⟨x, hxO x⟩) fun x ↦ ?_
  let f := Scheme.ProEt.ofOpenImmersionHom U (O x).ι
  rw [← hψ f, map_sectionAct, ← hψ f]
  have h1 : (g • m).comp f.left.base.hom = n x • m.comp f.left.base.hom := by
    ext y
    simp only [ContinuousMap.comp_apply, ContinuousMap.smul_apply', ContinuousMap.smul_apply]
    rw [show g (f.left.base y) = n x from hn x _ y.2, Nat.cast_smul_eq_nsmul]
  rw [h1, map_nsmul]
  have h2 : (adicConstantSheaf l X).obj.map f.op
      (ULift.up (ringValuedFunction ι hι hιE g)) =
        ULift.up (algebraMap _ _ ((ULift.up (n x : PadicAlgCl l) :
          ULift.{u + 1} (PadicAlgCl l))).down) := by
    refine ULift.ext (Subtype.ext (ContinuousMap.ext fun y ↦ ?_))
    change ι (g (f.left.base y)) = (n x : PadicAlgCl l)
    rw [show g (f.left.base y) = n x from hn x _ y.2, map_natCast]
  rw [h2, algebraMap_sectionAct]
  exact (Nat.cast_smul_eq_nsmul _ _ _).symm

end AlgebraicGeometry.ProEtale.AdicSheaf
