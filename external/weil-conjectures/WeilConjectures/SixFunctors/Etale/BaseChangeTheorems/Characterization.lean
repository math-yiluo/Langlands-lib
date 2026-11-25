/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Coefficients

/-!
# Three characterisations of the base change property

Let `f : X ⟶ Y` be a proper morphism of schemes. The following are equivalent
(`AlgebraicGeometry.Etale.tfae_hasTorsionBaseChange`):

1. `PBC(f)`: the derived base change map of every cartesian square over `f` is an isomorphism on
   every bounded below complex with torsion cohomology sheaves
   (`AlgebraicGeometry.Etale.HasTorsionBaseChange`);
2. the base change maps `g^* Rᵠf_* F ⟶ Rᵠf'_* g'^* F` on cohomology sheaves are isomorphisms for
   every torsion sheaf `F` and every `q`;
3. `IA(f)` with the coefficient rings `Λ ⧸ pΛ` for every prime `p`
   (`AlgebraicGeometry.Etale.HasInjectiveAcyclicity`).

The equivalence of (1) and (2) holds for every morphism
(`AlgebraicGeometry.Etale.hasTorsionBaseChange_iff_forall_isIso_baseChangeHomologyMap`): a complex
with torsion cohomology is built from its torsion cohomology sheaves by truncations. For abelian
sheaves, that is for `Λ = ℤ`, condition (3) is `IA_r(f)` with `𝐅_r`-coefficients for every prime
`r` (`AlgebraicGeometry.Etale.tfae_hasTorsionBaseChange_int`).

## References

- Stacks Project, Lemma 59.91.6, <https://stacks.math.columbia.edu/tag/0A4B>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}

/-- **The base change property on cohomology sheaves.** A morphism `f : X ⟶ Y` satisfies the base
change property for torsion coefficients if and only if, for every cartesian square over `f` and
every torsion sheaf `F` on `X_ét`, the base change maps `g^* Rᵠf_* F ⟶ Rᵠf'_*(g'^* F)` on
cohomology sheaves are isomorphisms for all `q`. The forward direction places `F` in degree `0`;
conversely a bounded below complex with torsion cohomology is reached from its cohomology sheaves
by truncation triangles, both sides of the derived base change map being left `t`-exact.
(blueprint: `theorem-pbc-injective-acyclicity`, equivalence of (1) and (2)) -/
theorem Etale.hasTorsionBaseChange_iff_forall_isIso_baseChangeHomologyMap (f : X ⟶ Y) :
    Etale.HasTorsionBaseChange Λ f ↔
      ∀ ⦃Y' X' : Scheme.{u}⦄ ⦃g : Y' ⟶ Y⦄ ⦃f' : X' ⟶ Y'⦄ ⦃g' : X' ⟶ X⦄
        (sq : IsPullback g' f' f g) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        IsTorsionModuleSheaf F → ∀ q, IsIso (Etale.baseChangeHomologyMap Λ sq q F) := by
  refine ⟨fun hf Y' X' g f' g' sq F hF q ↦ ?_, fun h Y' X' g f' g' sq K hK ↦ ?_⟩
  · have := hf sq _ (Etale.DerivedCategory.Plus.moduleTorsionHomology_singleFunctor_obj Λ X F)
    rw [← Etale.baseChange_eq_derivedBaseChangeMapPlus] at this
    exact (Etale.isIso_baseChange_app_singleFunctor_obj_iff Λ sq F).1 this q
  · rw [← Etale.baseChange_eq_derivedBaseChangeMapPlus]
    let P : ObjectProperty (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
      fun F ↦ IsTorsionModuleSheaf F
    have : P.IsClosedUnderIsomorphisms := ⟨fun e h ↦
      have : IsTorsionModuleSheaf _ := h
      IsTorsionModuleSheaf.of_epi e.hom⟩
    exact DerivedCategory.Plus.isIso_app_of_forall_homology _ P
      (fun F hF ↦ (Etale.isIso_baseChange_app_singleFunctor_obj_iff Λ sq F).2 (h sq F hF))
      (fun K n _ q hq ↦ Etale.isZero_homologyFunctor_baseChangeSource_obj Λ g f K n q hq)
      (fun K n _ q hq ↦ Etale.isZero_homologyFunctor_baseChangeTarget_obj Λ g' f' K n q hq) K hK

/-- **PBC and injective acyclicity.** For a proper morphism `f : X ⟶ Y` and a coefficient ring
`Λ`, the following are equivalent:

1. `f` satisfies the base change property for torsion coefficients;
2. for every cartesian square over `f` and every torsion sheaf `F`, the base change maps
   `g^* Rᵠf_* F ⟶ Rᵠf'_*(g'^* F)` are isomorphisms for all `q`;
3. `f` has injective acyclicity with `Λ ⧸ pΛ`-coefficients for every prime `p`.

(blueprint: `theorem-pbc-injective-acyclicity`) -/
@[stacks 0A4B]
theorem Etale.tfae_hasTorsionBaseChange (f : X ⟶ Y) [IsProper f] :
    List.TFAE [Etale.HasTorsionBaseChange Λ f,
      ∀ ⦃Y' X' : Scheme.{u}⦄ ⦃g : Y' ⟶ Y⦄ ⦃f' : X' ⟶ Y'⦄ ⦃g' : X' ⟶ X⦄
        (sq : IsPullback g' f' f g) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        IsTorsionModuleSheaf F → ∀ q, IsIso (Etale.baseChangeHomologyMap Λ sq q F),
      ∀ p : ℕ, p.Prime → Etale.HasInjectiveAcyclicity (Λ ⧸ Ideal.span {(p : Λ)}) f] := by
  tfae_have 1 ↔ 2 := Etale.hasTorsionBaseChange_iff_forall_isIso_baseChangeHomologyMap Λ f
  tfae_have 1 → 3 := fun hf p _ ↦ (hf.quotient Λ p).hasInjectiveAcyclicity _ f
  tfae_have 3 → 1 := Etale.hasTorsionBaseChange_of_hasInjectiveAcyclicity Λ f
  tfae_finish

/-- For a proper morphism and two isomorphic coefficient rings which are torsion as additive
groups, injective acyclicity with the one coefficient ring is injective acyclicity with the other:
both are the base change property, which transfers along ring homomorphisms. -/
theorem Etale.hasInjectiveAcyclicity_iff_of_ringEquiv {Λ' : Type (u + 1)} [CommRing Λ']
    (e : Λ ≃+* Λ') (hΛ : IsAddTorsion Λ) (f : X ⟶ Y) [IsProper f] :
    Etale.HasInjectiveAcyclicity Λ f ↔ Etale.HasInjectiveAcyclicity Λ' f := by
  have hΛ' : IsAddTorsion Λ' := fun x ↦ by
    obtain ⟨n, hn, h⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 (hΛ (e.symm x))
    exact isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, by simpa using congrArg e h⟩
  rw [← Etale.hasTorsionBaseChange_iff_hasInjectiveAcyclicity Λ hΛ,
    ← Etale.hasTorsionBaseChange_iff_hasInjectiveAcyclicity Λ' hΛ']
  exact ⟨fun h ↦ h.of_ringHom Λ e.toRingHom, fun h ↦ h.of_ringHom Λ' e.symm.toRingHom⟩

/-- **PBC and injective acyclicity, abelian sheaves.** For a proper morphism `f : X ⟶ Y` the
following are equivalent:

1. `PBC(f)`: the base change property for complexes of abelian sheaves (sheaves of
   `ULift ℤ`-modules) with torsion cohomology;
2. for every cartesian square over `f` and every torsion abelian sheaf `F`, the base change maps
   `g^* Rᵠf_* F ⟶ Rᵠf'_*(g'^* F)` are isomorphisms for all `q`;
3. `IA_r(f)` with `𝐅_r`-coefficients holds for every prime `r`
   (`AlgebraicGeometry.Etale.HasAllPrimeInjectiveAcyclicity`).

(blueprint: `theorem-pbc-injective-acyclicity`) -/
@[stacks 0A4B]
theorem Etale.tfae_hasTorsionBaseChange_int (f : X ⟶ Y) [IsProper f] :
    List.TFAE [Etale.HasTorsionBaseChange (ULift.{u + 1} ℤ) f,
      ∀ ⦃Y' X' : Scheme.{u}⦄ ⦃g : Y' ⟶ Y⦄ ⦃f' : X' ⟶ Y'⦄ ⦃g' : X' ⟶ X⦄
        (sq : IsPullback g' f' f g)
        (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))),
        IsTorsionModuleSheaf F →
          ∀ q, IsIso (Etale.baseChangeHomologyMap (ULift.{u + 1} ℤ) sq q F),
      Etale.HasAllPrimeInjectiveAcyclicity f] := by
  have h := Etale.tfae_hasTorsionBaseChange (ULift.{u + 1} ℤ) f
  have h₃ : (∀ p : ℕ, p.Prime → Etale.HasInjectiveAcyclicity
      (ULift.{u + 1} ℤ ⧸ Ideal.span {(p : ULift.{u + 1} ℤ)}) f) ↔
      Etale.HasAllPrimeInjectiveAcyclicity f :=
    forall₂_congr fun p hp ↦ by
      -- `ULift ℤ ⧸ pℤ ≃ ULift (ZMod p)`
      let e : ULift.{u + 1} ℤ ⧸ Ideal.span {(p : ULift.{u + 1} ℤ)} ≃+* ULift.{u + 1} (ZMod p) :=
        (Ideal.quotientEquiv _ (Ideal.span {(p : ℤ)}) ULift.ringEquiv (by
          rw [Ideal.map_span, Set.image_singleton]
          simp)).trans ((Int.quotientSpanNatEquivZMod p).trans ULift.ringEquiv.symm)
      exact Etale.hasInjectiveAcyclicity_iff_of_ringEquiv _ e
        (isAddTorsion_quotient_span_natCast _ hp.pos) f
  rw [h₃] at h
  exact h

end AlgebraicGeometry
