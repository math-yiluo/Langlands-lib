/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Fourier
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraTwist
public import WeilConjectures.WeilSheaf.IhomLisse.Comp

/-!
# Iterated internal homs of pro-étale Weil sheaves

The comparison `[[[a, H], L], K] ⟶ [a, [[H, L], K]]` (`CategoryTheory.Mod.ihomIhomComparison`)
is compatible with the Weil structures
(`AlgebraicGeometry.ProEtaleWeilSheaf.ihomIhomComparison_comm`):
the Frobenius pullback `Fr^* = (Fr⁻¹)_*` is a lax braided functor whose comparison with the
internal hom is compatible with the evaluations, and the Weil structure of an internal hom is the
transport of the Weil structures of its arguments. For `a` lisse it is an isomorphism
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.isIso_ihomIhomComparison`), which gives
`AlgebraicGeometry.ProEtaleWeilSheaf.ihomFunctorIsoIhomFunctorCompIhomFunctor`:
`[[[a, H], L], -] ≅ [a, [[H, L], -]]`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Endofunctor

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

attribute [local instance] Sheaf.symmetricCategory

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

variable (k₀ l X) in
/-- The comparison `Fr^* 𝓗om(M, N) ⟶ 𝓗om(Fr^* M, Fr^* N)` for the Frobenius pullback. -/
noncomputable abbrev frobeniusIhomComparison
    (M N : AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    (WeilSheaf.frobeniusPullback k₀ l X).obj ((AdicSheaf.ihom M).obj N) ⟶
      (AdicSheaf.ihom ((WeilSheaf.frobeniusPullback k₀ l X).obj M)).obj
        ((WeilSheaf.frobeniusPullback k₀ l X).obj N) :=
  (adicLowerStarCompIhomIso l (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv
    M).inv.app N

/-- The comparison for the Frobenius pullback, an automorphism, is an isomorphism. -/
instance (M N : AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    IsIso (frobeniusIhomComparison k₀ l X M N) := by
  unfold frobeniusIhomComparison
  infer_instance

/-- The uncurried form of the comparison is the Frobenius pullback of the evaluation. -/
lemma uncurryHom_frobeniusIhomComparison
    (M N : AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    Mod.uncurryHom (frobeniusIhomComparison k₀ l X M N) =
      Functor.LaxMonoidal.μ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[
        WeilCoefficients.{u} l] _ _ ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[_].map
          (Mod.evaluation M N) := by
  have : (Mod.mapModComap
      (G := ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[
        WeilCoefficients.{u} l]) (adicConstantSheafToLowerStar l
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)).IsEquivalence :=
    isEquivalence_adicLowerStar l _
  exact (Mod.μ_comp_map_evaluation (adicConstantSheafToLowerStar l
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)
    (fun _ _ ↦ Functor.LaxBraided.braided _ _) M N).symm

/-- The Weil structure of the internal hom is the transport of the Weil structures. -/
lemma ihom_str_eq_trIso (A B : ProEtaleWeilSheaf k₀ l X) :
    (ihom k₀ l X A B).str = Mod.trIso (adicConstantSheafToLowerStar l
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)
      (fun M N ↦ frobeniusIhomComparison k₀ l X M N) A.str B.str := by
  unfold ProEtaleWeilSheaf.ihom
  rw [IsoAlgebra.mk_str]
  exact Iso.ext rfl

/-- **The comparison `[[[a, H], L], K] ⟶ [a, [[H, L], K]]` is compatible with the Weil
structures.** -/
theorem ihomIhomComparison_comm (a H L K : ProEtaleWeilSheaf k₀ l X) :
    (WeilSheaf.frobeniusPullback k₀ l X).map
        (Mod.ihomIhomComparison a.carrier H.carrier L.carrier K.carrier) ≫
      (ihom k₀ l X a (ihom k₀ l X (ihom k₀ l X H L) K)).obj.str =
    (ihom k₀ l X (ihom k₀ l X (ihom k₀ l X a H) L) K).obj.str ≫
      Mod.ihomIhomComparison a.carrier H.carrier L.carrier K.carrier := by
  rw [← IsoAlgebra.str_hom, ← IsoAlgebra.str_hom]
  exact Mod.map_ihomIhomComparison_comp_of_eq
    (G := ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)_*[
      WeilCoefficients.{u} l])
    (ρ := adicConstantSheafToLowerStar l
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv)
    (c := fun M N ↦ frobeniusIhomComparison k₀ l X M N) uncurryHom_frobeniusIhomComparison
    (fun _ _ ↦ Functor.LaxBraided.braided _ _) a.str H.str L.str K.str
    _ (ihom_str_eq_trIso H L) _ (ihom_str_eq_trIso a H) _
    (ihom_str_eq_trIso (ihom k₀ l X a H) L) _ (ihom_str_eq_trIso (ihom k₀ l X H L) K) _
    (ihom_str_eq_trIso (ihom k₀ l X (ihom k₀ l X a H) L) K) _
    (ihom_str_eq_trIso a (ihom k₀ l X (ihom k₀ l X H L) K))

variable [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- **Iterated internal homs out of a lisse pro-étale Weil sheaf**:
`[[[a, H], L], -] ≅ [a, [[H, L], -]]` for `a` lisse. -/
noncomputable def ihomFunctorIsoIhomFunctorCompIhomFunctor (a H L : ProEtaleWeilSheaf k₀ l X)
    (ha : IsAdicLisseSheaf a.carrier) :
    ihomFunctor k₀ l X (ihom k₀ l X (ihom k₀ l X a H) L) ≅
      ihomFunctor k₀ l X (ihom k₀ l X H L) ⋙ ihomFunctor k₀ l X a :=
  NatIso.ofComponents (fun K ↦
    have := ha.isIso_ihomIhomComparison H.carrier L.carrier K.carrier
    IsoAlgebra.isoMk (asIso (Mod.ihomIhomComparison a.carrier H.carrier L.carrier K.carrier))
      (ihomIhomComparison_comm a H L K))
    fun f ↦ IsoAlgebra.hom_ext (Mod.ihomIhomComparison_naturality_right _ _ _ f.hom.f)

end AlgebraicGeometry.ProEtaleWeilSheaf
