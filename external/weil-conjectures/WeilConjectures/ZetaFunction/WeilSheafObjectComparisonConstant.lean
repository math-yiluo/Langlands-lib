/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantGlobalSections
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseRankCriterion
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseStalk
public import WeilConjectures.SixFunctors.ProEtale.Adic.TwistedSection
public import WeilConjectures.WeilSheaf.GeometricallyConstant
public import WeilConjectures.ZetaFunction.WeilSheafObjectComparisonSpec

/-!
# Geometrically constant Weil sheaves have the local traces of Weil objects

Let `G` be a geometrically constant Weil sheaf on a separated `k₀`-scheme `X₀` of finite type
whose geometric fiber `X̄ = X₀ ⊗ k̄` is connected, so that its underlying sheaf is `ℚ̄_ℓʳ` on all
of `X̄` (`AlgebraicGeometry.WeilSheaf.IsGeometricallyConstant.exists_iso_biproduct_unit`). This
is the case of Deligne's descent statement (Weil II, 1.3.14) where everything is explicit: `G`
is determined by the Frobenius `F` acting on `V = Γ(X̄, G)`, and the trace function of `G` at
an `𝔽_{q^{n+1}}`-point is `Tr(F^{n+1} | V) = ∑ λ^{n+1}`, the sum running over the eigenvalues
`λ` of `F` with multiplicity, independently of the point.

Indeed, on the connected `X̄` the restriction `Γ(X̄, ℚ̄_ℓʳ) ⟶ (ℚ̄_ℓʳ)_s` of global sections to
the stalk at any geometric point `s` is bijective
(`AlgebraicGeometry.ProEtale.bijective_globalSectionsToUpperStar_of_iso_biproduct_unit`): both
sides are `r`-dimensional, and a global section `β : ℚ̄_ℓ ⟶ ℚ̄_ℓʳ` vanishing at `s` vanishes,
every nonzero coordinate of `β` being invertible on the connected `X̄`. This restriction
intertwines `F^{n+1}` with the local Frobenius at a point of degree `n + 1`.

On the side of the Weil objects, the direct sum of the units of `Dᵇc(X₀)⟦ℚ̲̄_ℓ⟧` twisted by the
eigenvalues `λ` (`ProEtale.CondensedRing.exists_weilBoundedConstructible_trace_eq_sum_pow`) has
local traces `∑ λ^{n+1}` at every point of degree `n + 1`.

## Main results

- `AlgebraicGeometry.ProEtale.bijective_globalSectionsToUpperStar_of_iso_biproduct_unit`: on a
  connected scheme the global sections of `ℚ̄_ℓʳ` are its stalk at any point.
- `AlgebraicGeometry.WeilSheaf.IsGeometricallyConstant.traceFunction_eq_trace_globalSections`:
  the trace function of a geometrically constant Weil sheaf is the trace of the powers of the
  Frobenius on its global sections.
- `WeilSheaf.IsGeometricallyConstant.exists_weilBoundedConstructible_traceFunction`, in the
  namespace `AlgebraicGeometry`: the *local clause* of the comparison
  `AlgebraicGeometry.WeilComplex.HasWeilObjectComparison` for geometrically constant Weil
  sheaves.

## Implementation notes

Only the local clause of `AlgebraicGeometry.WeilComplex.HasWeilObjectComparison` is proved here.
The global clause asks that the global traces of the same Weil object, namely
`∑ λ^{n+1} · #X₀(𝔽_{q^{n+1}})`, be the alternating sums of the traces of `F^{n+1}` on the
compactly supported cohomology `H_c^i(X̄, G) ≅ H_c^i(X̄, ℚ̄_ℓ) ⊗ V`. This is the
Grothendieck–Lefschetz trace formula for the constant sheaf `ℚ̄_ℓ` on `X₀` in the model of the
Weil sheaves, which is not available for general `X₀` (on `X₀ = Spec k₀` it is
`AlgebraicGeometry.WeilSheaf.hasWeilObjectComparison_toComplex_spec`).

The connectedness of `X̄` is assumed: on a disconnected `X̄` the Frobenius permutes the
connected components and the trace function of a geometrically constant Weil sheaf depends on
the component of the point, so it is not of the form `∑ λ^{n+1}`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

/-- On a connected scheme `Z`, the global sections of `ℚ̄_ℓʳ` form an `r`-dimensional space. -/
theorem finrank_globalSections_biproduct_unit_of_connectedSpace (Z : Scheme.{u})
    [ConnectedSpace Z] (n : ℕ) :
    Module.finrank (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj
      ((Sheaf.Γ (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)).obj
        (⨁ fun _ : Fin n ↦ AdicSheaf.unit l Z).X)) = n := by
  have : (Sheaf.Γ (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)).Additive :=
    Functor.additive_of_preserves_binary_products _
  let G := Sheaf.Γ (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l) ⋙
    WeilCoefficients.toModuleCat l
  let e' : G.obj (⨁ fun _ : Fin n ↦ AdicSheaf.unit l Z).X ≅
      ModuleCat.of _ (Fin n → G.obj (adicConstantSheaf l Z)) :=
    G.mapIso ((AdicSheaf.forget _).mapBiproduct (fun _ : Fin n ↦ AdicSheaf.unit l Z)) ≪≫
      G.mapBiproduct (fun _ : Fin n ↦ adicConstantSheaf l Z) ≪≫
      ModuleCat.biproductIsoPi (fun _ : Fin n ↦ G.obj (adicConstantSheaf l Z))
  have h1 : Module.finrank (PadicAlgCl l) (G.obj (adicConstantSheaf l Z)) = 1 :=
    finrank_globalSections_adicConstantSheaf Z
  have : FiniteDimensional (PadicAlgCl l) (G.obj (adicConstantSheaf l Z)) :=
    Module.finite_of_finrank_eq_succ h1
  calc _ = Module.finrank (PadicAlgCl l) (Fin n → G.obj (adicConstantSheaf l Z)) :=
        e'.toLinearEquiv.finrank_eq
    _ = n := by
      rw [Module.finrank_pi_fintype, h1]
      simp

/-- On a connected scheme `Z`, a morphism `β : ℚ̄_ℓ ⟶ M` into a sheaf `M ≅ ℚ̄_ℓʳ` whose pullback
to a point `s : Spec K ⟶ Z` vanishes is zero: a nonzero coordinate of `β` would be invertible,
and so would be its pullback to `s`, while `s^* ℚ̄_ℓ ≅ ℚ̄_ℓ` is nonzero. -/
lemma eq_zero_of_adicUpperStar_map_eq_zero_of_iso_biproduct_unit {Z : Scheme.{u}}
    [ConnectedSpace Z] {K : Type u} [Field K] (s : Spec (.of K) ⟶ Z) {M : AdicSheaf l Z}
    {n : ℕ} (e : M ≅ ⨁ fun _ : Fin n ↦ AdicSheaf.unit l Z) {β : AdicSheaf.unit l Z ⟶ M}
    (hβ : (s)^*ᵃ[l].map β = 0) : β = 0 := by
  rw [← cancel_mono e.hom, zero_comp]
  refine biproduct.hom_ext _ _ fun j ↦ ?_
  rw [zero_comp]
  by_contra h
  have : IsIso (β ≫ e.hom ≫ biproduct.π _ j) := AdicSheaf.isIso_of_ne_zero (by simpa using h)
  have hz : IsZero ((s)^*ᵃ[l].obj (AdicSheaf.unit l Z)) := by
    rw [IsZero.iff_id_eq_zero, ← (s)^*ᵃ[l].map_id, ← IsIso.hom_inv_id
      (β ≫ e.hom ≫ biproduct.π _ j), Functor.map_comp, Functor.map_comp, hβ, zero_comp,
      zero_comp]
  exact not_isZero_adicConstantSheaf l (Spec (.of K))
    ((AdicSheaf.forget _).map_isZero (hz.of_iso (adicUpperStarUnitIso l s).symm))

/-- **The global sections of `ℚ̄_ℓʳ` on a connected scheme are its stalk.** On a connected
scheme `Z`, for a sheaf `M ≅ ℚ̄_ℓʳ` and a point `s : Spec K ⟶ Z` with finite-dimensional stalk,
the restriction `Γ(Z, M) ⟶ Γ(Spec K, s^* M)` is bijective: it is injective
(`AlgebraicGeometry.ProEtale.eq_zero_of_adicUpperStar_map_eq_zero_of_iso_biproduct_unit`) and
both sides are `r`-dimensional. -/
theorem bijective_globalSectionsToUpperStar_of_iso_biproduct_unit {Z : Scheme.{u}}
    [ConnectedSpace Z] {K : Type u} [Field K] (s : Spec (.of K) ⟶ Z) {M : AdicSheaf l Z}
    {n : ℕ} (e : M ≅ ⨁ fun _ : Fin n ↦ AdicSheaf.unit l Z)
    (hfin : FiniteDimensional (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj
      (((s)^*[WeilCoefficients.{u} l] ⋙ Sheaf.Γ _ (WeilCoefficients.{u} l)).obj M.X))) :
    Function.Bijective ((WeilCoefficients.toModuleCat l).map
      ((globalSectionsToUpperStar (WeilCoefficients.{u} l) s).app M.X)).hom := by
  set f := ((WeilCoefficients.toModuleCat l).map
    ((globalSectionsToUpperStar (WeilCoefficients.{u} l) s).app M.X)).hom
  have hinj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun a ha ↦ ?_
    obtain ⟨β, rfl⟩ := (bijective_globalSectionOfModHom M).2 a
    have hβ : globalSectionOfModHom ((adicUpperStarUnitIso l s).inv ≫ (s)^*ᵃ[l].map β) =
        globalSectionOfModHom (0 : AdicSheaf.unit l _ ⟶ (s)^*ᵃ[l].obj M) := by
      rw [← globalSectionsToUpperStar_globalSectionOfModHom, globalSectionOfModHom_zero]
      exact ha
    have hβ' := (bijective_globalSectionOfModHom _).1 hβ
    rw [← cancel_epi (adicUpperStarUnitIso l s).hom, Iso.hom_inv_id_assoc, comp_zero] at hβ'
    rw [eq_zero_of_adicUpperStar_map_eq_zero_of_iso_biproduct_unit s e hβ',
      globalSectionOfModHom_zero]
  have : FiniteDimensional (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj
      ((Sheaf.Γ (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)).obj M.X)) :=
    Module.Finite.of_injective f hinj
  have hdom : Module.finrank (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj
      ((Sheaf.Γ (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)).obj M.X)) = n :=
    (WeilCoefficients.linearEquivOfIso ((Sheaf.Γ _ _).mapIso
      ((AdicSheaf.forget _).mapIso e))).finrank_eq.trans
        (finrank_globalSections_biproduct_unit_of_connectedSpace Z n)
  have hcod : Module.finrank (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj
      (((s)^*[WeilCoefficients.{u} l] ⋙ Sheaf.Γ _ (WeilCoefficients.{u} l)).obj M.X)) = n :=
    (WeilCoefficients.linearEquivOfIso ((AdicSheaf.fibre l s).mapIso e)).finrank_eq.trans
      (AdicSheaf.finrank_fibre_free s n)
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (hdom.trans hcod.symm)).1 hinj⟩

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.WeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section TraceFunction

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [ConnectedSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]

/-- **The trace function of a geometrically constant Weil sheaf.** If the geometric fiber `X̄`
is connected, the trace function of a geometrically constant Weil sheaf `G` at an
`𝔽_{qᵐ}`-point, `m ≥ 1`, is the trace of `Fᵐ` on the global sections `Γ(X̄, G)`: the
restriction to the stalk at the geometric point over the point is a linear isomorphism
intertwining `Fᵐ` with the local Frobenius. -/
theorem IsGeometricallyConstant.traceFunction_eq_trace_globalSections {G : WeilSheaf k₀ l X}
    (hG : G.IsGeometricallyConstant) (m : ℕ) (hm : 1 ≤ m)
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ m)) :
    G.traceFunction m y =
      LinearMap.trace (PadicAlgCl l) _ (G.globalSections.frobeniusEnd ^ m) := by
  have : Finite (FiniteField.galoisExtension k₀ m) := Module.finite_of_finite k₀
  obtain ⟨n, ⟨e⟩⟩ := hG.exists_iso_biproduct_unit
  set s := (X ↘ Spec (CommRingCat.of k₀)).geometricFiberPoint IsAlgClosed.lift y.1 y.2
  have hs := Scheme.Hom.geometricFiberPoint_fieldPoints_comp_geometricGaloisFrobenius_pow
    (X ↘ Spec (CommRingCat.of k₀)) m IsAlgClosed.lift y
  let e' : G.globalSections.carrier ≃ₗ[PadicAlgCl l] (G.stalkAt s m hs).carrier :=
    LinearEquiv.ofBijective (G.globalSectionsToStalkAt s m hs)
      (bijective_globalSectionsToUpperStar_of_iso_biproduct_unit s e
        (G.finiteDimensional_stalkObj s))
  have he : e'.toLinearMap = G.globalSectionsToStalkAt s m hs := rfl
  have hcomp := G.globalSectionsToStalkAt_comp_frobeniusEnd_pow s m hm hs
  rw [← he] at hcomp
  exact LinearMap.trace_eq_of_linearEquiv_comp_eq e' hcomp

end TraceFunction

attribute [local instance] fact_ringChar_prime_of_finite

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [ConnectedSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]

open ProEtale.CondensedRing in
/-- **Geometrically constant Weil sheaves have the local traces of Weil objects** (the local
clause of `AlgebraicGeometry.WeilComplex.HasWeilObjectComparison`). If the geometric fiber `X̄`
is connected, the trace function of a geometrically constant Weil sheaf `G` in degree `n + 1` is
`Tr(F^{n+1} | Γ(X̄, G)) = ∑ λ^{n+1}` over the eigenvalues `λ` of the Frobenius `F`, and those
are the local traces of the direct sum of the units twisted by the `λ`. -/
theorem IsGeometricallyConstant.exists_weilBoundedConstructible_traceFunction
    {G : WeilSheaf k₀ l X} (hG : G.IsGeometricallyConstant) :
    ∃ K' : WeilBoundedConstructible l (Iso.refl (WeilComplex.overSpec (k₀ := k₀) X)).hom,
      ∀ (n : ℕ) (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints
          (FiniteField.galoisExtension k₀ (n + 1))),
        endTensorUnitRingEquiv l (AlgebraicClosure k₀)
          (weilStalkTraceAlternatingSum l (n + 1) _
            (frobeniusFixedPointsReflOfFieldPoint (X := WeilComplex.overSpec X) n y).2.2 K') =
          (toComplex.obj G).traceFunction (n + 1) y := by
  set f := G.globalSections.frobeniusEnd
  have hdet : IsUnit (LinearMap.det f) := LinearEquiv.isUnit_det' G.globalSections.frobenius
  let s : Multiset (_root_.PadicAlgCl l)ˣ := f.charpoly.roots.pmap (fun a ha ↦ Units.mk0 a ha)
    fun a ha h0 ↦ LinearMap.zero_notMem_roots_charpoly hdet (h0 ▸ ha)
  have hs (m : ℕ) : (s.map fun c : (_root_.PadicAlgCl l)ˣ ↦ (c : _root_.PadicAlgCl l) ^ m).sum =
      LinearMap.trace (_root_.PadicAlgCl l) _ (f ^ m) := by
    rw [LinearMap.trace_pow_eq_sum_pow_roots_charpoly, Multiset.map_pmap]
    exact congrArg Multiset.sum (Multiset.pmap_eq_map _ _ _ _)
  obtain ⟨K, hl, -⟩ := exists_weilBoundedConstructible_trace_eq_sum_pow l
    (X := WeilComplex.overSpec (k₀ := k₀) X) s
  refine ⟨K, fun n y ↦ ?_⟩
  rw [hl, hs, WeilComplex.traceFunction_toComplex,
    hG.traceFunction_eq_trace_globalSections (n + 1) (by omega) y]

end AlgebraicGeometry.WeilSheaf
