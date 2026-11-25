/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.IsLE
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedSupportAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.EtaleDuality
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.HomDevissage

/-!
# The derived hom out of a constructible complex has bounded amplitude

Let `k` be a field, `X` a scheme of finite type over `k` and `Λ` a finite ring. For
`K ∈ Dctf(X_ét, Λ)` the functor `RHom(K, -)` raises the upper bound of bounded complexes by a
uniform amount: there is `B` with `RHom(K, L) ∈ D^{≤ b + B}` for every `L` with homology in
`[a, b]` (`AlgebraicGeometry.Etale.exists_isLE_derivedHom_of_constructibleFiniteTor`).

The proof is a dévissage in `K` (`definition-verdier-dual-evaluation--3`): such `K` form a thick
subcategory, and on the generators `K = Rg_* Rj_! P`, with `g` a closed and `j` an open immersion
and `P` lisse flat, `RHom(K, L) ≅ Rg_* Rj_* RHom(P, Rj^! Rg^! L)` (as in
`AlgebraicGeometry.Etale.constructibleFiniteTor_derivedHom_of_field`). Each functor in this
composite has bounded amplitude: `Rg^!` by the closed-support triangle
(`AlgebraicGeometry.Etale.homologyConcentratedIn_rightDerivedUpperShriek`), `Rj^! ≅ Lj^*` is
exact, `RHom(P, -) ≅ P^∨ ⊗ᴸ -`, and `Rg_*`, `Rj_*` raise degrees by at most twice the dimension
(`AlgebraicGeometry.Etale.isLE_rightDerivedLowerStar_obj`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite ZeroObject Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The objects `K` of `D(X_ét, Λ)` for which `RHom(K, -)` raises the upper bound of bounded
complexes by a uniform amount: for some `B`, `RHom(K, L)` vanishes above `b + B` whenever `L`
has homology in `[a, b]`. -/
def derivedHomBoundedAmplitude (X : Scheme.{u}) :
    ObjectProperty (_root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  fun K ↦ ∃ B : ℤ, ∀ (a b : ℤ)
    (L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      _root_.DerivedCategory.homologyConcentratedIn a b L →
        (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K)).obj L).IsLE (b + B)

instance (X : Scheme.{u}) : (derivedHomBoundedAmplitude Λ X).IsTriangulated where
  exists_zero := ⟨0, isZero_zero _, 0, fun _ _ L _ ↦
    _root_.DerivedCategory.TStructure.t.isLE_of_isZero
      (isZero_derivedHom_obj_of_isZero _ (isZero_zero _) L) _⟩
  isStableUnderShiftBy n := ⟨fun K ⟨B, hB⟩ ↦ ⟨B + n, fun a b L hL ↦ by
    have := hB a b L hL
    have : (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op K) ⋙ shiftFunctor _ (-n)).obj L).IsLE
        (b + (B + n)) :=
      _root_.DerivedCategory.TStructure.t.isLE_shift _ (b + B) (-n) _
    exact _root_.DerivedCategory.TStructure.t.isLE_of_iso
      ((derivedHomShiftIso (ModuleCat.{u + 1} Λ) K n).app L).symm _⟩⟩
  ext₂' T hT h₁ h₃ := by
    obtain ⟨B₁, hB₁⟩ := h₁
    obtain ⟨B₃, hB₃⟩ := h₃
    refine ObjectProperty.le_isoClosure _ _ ⟨max B₁ B₃, fun a b L hL ↦ ?_⟩
    obtain ⟨w, hw⟩ := exists_distTriang_derivedHom_left L T hT
    have := hB₁ a b L hL
    have := hB₃ a b L hL
    have h₁ : (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op T.obj₁)).obj L).IsLE (b + max B₁ B₃) :=
      _root_.DerivedCategory.TStructure.t.isLE_of_le _ (b + B₁) _ (by lia)
    have h₃ : (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op T.obj₃)).obj L).IsLE (b + max B₁ B₃) :=
      _root_.DerivedCategory.TStructure.t.isLE_of_le _ (b + B₃) _ (by lia)
    exact _root_.DerivedCategory.TStructure.t.isLE₂ _ hw _ h₃ h₁

instance (X : Scheme.{u}) : (derivedHomBoundedAmplitude Λ X).IsClosedUnderIsomorphisms :=
  ⟨fun {K K'} e ⟨B, hB⟩ ↦ ⟨B, fun a b L hL ↦ by
    have : (((RHom(X)[ModuleCat.{u + 1} Λ]).flip.obj L).obj (op K)).IsLE (b + B) := hB a b L hL
    exact _root_.DerivedCategory.TStructure.t.isLE_of_iso
      ((((RHom(X)[ModuleCat.{u + 1} Λ]).flip.obj L).mapIso e.op).symm) _⟩⟩

instance (X : Scheme.{u}) : (derivedHomBoundedAmplitude Λ X).IsStableUnderRetracts :=
  ⟨fun {K K'} e ⟨B, hB⟩ ↦ ⟨B, fun a b L hL ↦ by
    have : (((RHom(X)[ModuleCat.{u + 1} Λ]).flip.obj L).obj (op K')).IsLE (b + B) := hB a b L hL
    exact _root_.DerivedCategory.isLE_of_retract
      (e.op.map ((RHom(X)[ModuleCat.{u + 1} Λ]).flip.obj L)) _⟩⟩

variable {Λ} {k : Type u} [Field k]

/-- The higher direct images along a morphism `f : X ⟶ Y` of `k`-schemes of finite type with
`dim X ≤ d`, `k` any field, vanish above `2d`
(`AlgebraicGeometry.Etale.isZero_rightDerived_lowerStar_of_two_mul_lt`). -/
lemma isZero_higherDirectImage_of_topologicalKrullDim_le {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY] (f : X ⟶ Y) (hf : f ≫ aY = aX) (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (hq : 2 * d < q) :
    IsZero (higherDirectImage Λ f q F) :=
  (isZero_rightDerived_lowerStar_of_two_mul_lt Λ isAddTorsion_of_finite aX aY f hf d hd F q
    hq).of_iso ((((f)_*[ModuleCat.{u + 1} Λ]).homologyRightDerivedFunctorObjSingleFunctorIso F
      q).symm ≪≫ homologyRightDerivedLowerStarSingleIsoHigherDirectImage Λ f F q).symm

/-- The exceptional inverse image along a closed immersion `g : Z ⟶ X` into a scheme of finite
type over `k` raises the upper bound of bounded complexes by a uniform amount: by the
closed-support triangle (`AlgebraicGeometry.Etale.homologyConcentratedIn_rightDerivedUpperShriek`),
as the higher direct images along the open complement vanish above twice its dimension. -/
lemma exists_isLE_rightDerivedUpperShriek_of_isClosedImmersion {X Z : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] (g : Z ⟶ X)
    [IsClosedImmersion g] [HasCompactification g] :
    ∃ c : ℤ, ∀ (a b : ℤ)
      (L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
        _root_.DerivedCategory.homologyConcentratedIn a b L →
          ((R(g)^![Λ]).obj L).IsLE (b + c) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian aX }
  let V : X.Opens := ⟨(Set.range g.base)ᶜ, g.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hij : Set.range g.base = (Set.range V.ι.base)ᶜ := by
    rw [Scheme.Opens.range_ι]
    simp [V]
  have : TopologicalSpace.NoetherianSpace V.toScheme :=
    V.ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  have : QuasiCompact V.ι := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le (V.ι ≫ aX)
  refine ⟨2 * d + 1, fun a b L hL ↦ ?_⟩
  have := (homologyConcentratedIn_rightDerivedUpperShriek g V.ι hij
    (isZero_higherDirectImage_of_topologicalKrullDim_le (V.ι ≫ aX) aX V.ι rfl d hd)
    hL).2
  exact _root_.DerivedCategory.TStructure.t.isLE_of_le _ (b + ((2 * d : ℕ) : ℤ) + 1) _
    (by push_cast; lia)

/-- The derived pullback along an open immersion `j` is exact; in particular
`Rj^! ≅ Lj^*` preserves the vanishing above a degree. -/
lemma isLE_rightDerivedUpperShriek_obj_of_isOpenImmersion {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [HasCompactification j]
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (n : ℤ)
    [M.IsLE n] : ((R(j)^![Λ]).obj M).IsLE n := by
  have := ((j)^*[ModuleCat.{u + 1} Λ]).isLE_mapDerivedCategory_obj M n
  exact _root_.DerivedCategory.TStructure.t.isLE_of_iso
    (((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j).app M).symm ≪≫
      ((Adjunction.rightAdjointUniq (rightDerivedUpperShriekAdjunction Λ j)
        (rightDerivedLowerShriekEtaleAdjunction Λ j)).app M).symm) n

/-- The generator case: for `j : U ⟶ Ū` an open immersion, `g : Ū ⟶ X` a closed immersion and
`P` a lisse flat sheaf on `U`, `RHom(Rg_* Rj_! P, -) ≅ Rg_* Rj_* RHom(P, Rj^! Rg^! -)` raises
the upper bound of bounded complexes by a uniform amount. -/
lemma derivedHomBoundedAmplitude_rightDerivedLowerStar_rightDerivedLowerShriek
    {X Ubar U : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    (j : U ⟶ Ubar) [IsOpenImmersion j] [HasCompactification j] [QuasiCompact j]
    (g : Ubar ⟶ X) [IsClosedImmersion g]
    (P : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsFiniteLocallyConstantSheaf P]
    (hP : ObjectProperty.flat P) :
    derivedHomBoundedAmplitude Λ X ((R((g)_*[ModuleCat.{u + 1} Λ])).obj
      ((R(j)_![ModuleCat.{u + 1} Λ]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj P))) := by
  have hΛ : IsAddTorsion Λ := isAddTorsion_of_finite
  let P₀ := (_root_.DerivedCategory.singleFunctor
    (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj P
  let N := (R(j)_![ModuleCat.{u + 1} Λ]).obj P₀
  obtain ⟨c, hc⟩ := exists_isLE_rightDerivedUpperShriek_of_isClosedImmersion (Λ := Λ) aX g
  obtain ⟨D, ⟨-, p, q, hDt⟩, ⟨_⟩⟩ :=
    exists_exactPairing_singleFunctor_of_isFiniteLocallyConstantSheaf Λ P hP
  have : D.IsLE q := (_root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn hDt).2
  obtain ⟨_⟩ := nonempty_exactPairing_swap D P₀
  have hKd : IsDualizable P₀ := ⟨⟨D⟩⟩
  obtain ⟨dU, hdU⟩ := exists_topologicalKrullDim_le (j ≫ g ≫ aX)
  obtain ⟨dV, hdV⟩ := exists_topologicalKrullDim_le (g ≫ aX)
  refine ⟨c + q + 2 * dU + 2 * dV, fun a b L hL ↦ ?_⟩
  let M := (R(g)^![Λ]).obj L
  have : M.IsLE (b + c) := hc a b L hL
  have : ((R(j)^![Λ]).obj M).IsLE (b + c) :=
    isLE_rightDerivedUpperShriek_obj_of_isOpenImmersion j M _
  -- `RHom(P, Rj^! M) ≅ P^∨ ⊗ᴸ Rj^! M`
  obtain ⟨e⟩ := nonempty_iso_coefficientDual_tensor hKd ((R(j)^![Λ]).obj M)
  have : ((coefficientDual (ModuleCat.{u + 1} Λ) U).obj (op P₀)).IsLE q :=
    _root_.DerivedCategory.TStructure.t.isLE_of_iso (coefficientDualIsoOfExactPairing D P₀).symm q
  have : (((RHom(U)[ModuleCat.{u + 1} Λ]).obj (op P₀)).obj ((R(j)^![Λ]).obj M)).IsLE
      (q + (b + c)) :=
    _root_.DerivedCategory.isLE_of_iso_of_isLE e (isLE_derivedTensor_obj _ U _ _ q (b + c))
  -- `Rj_* RHom(P, Rj^! M) ≅ RHom(Rj_! P, M)`
  have : ((R((j)_*[ModuleCat.{u + 1} Λ])).obj
      (((RHom(U)[ModuleCat.{u + 1} Λ]).obj (op P₀)).obj ((R(j)^![Λ]).obj M))).IsLE
      (q + (b + c) + 2 * dU) :=
    isLE_rightDerivedLowerStar_obj Λ hΛ (j ≫ g ≫ aX) (g ≫ aX) j rfl dU hdU _ _
  have : (((RHom(Ubar)[ModuleCat.{u + 1} Λ]).obj (op N)).obj M).IsLE (q + (b + c) + 2 * dU) :=
    _root_.DerivedCategory.isLE_of_iso_of_isLE
      (((derivedHomRightDerivedLowerShriekIsoOfFinite Λ j).app (op P₀)).app M) this
  -- `Rg_* RHom(N, Rg^! L) ≅ RHom(Rg_! N, L)`
  have : ((R((g)_*[ModuleCat.{u + 1} Λ])).obj
      (((RHom(Ubar)[ModuleCat.{u + 1} Λ]).obj (op N)).obj M)).IsLE
      (q + (b + c) + 2 * dU + 2 * dV) :=
    isLE_rightDerivedLowerStar_obj Λ hΛ (g ≫ aX) aX g rfl dV hdV _ _
  have : (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op ((R(g)_![ModuleCat.{u + 1} Λ]).obj N))).obj
      L).IsLE (q + (b + c) + 2 * dU + 2 * dV) :=
    _root_.DerivedCategory.isLE_of_iso_of_isLE
      (((derivedHomRightDerivedLowerShriekIsoOfFinite Λ g).app (op N)).app L) this
  -- `Rg_! ≅ Rg_*`
  have : (((RHom(X)[ModuleCat.{u + 1} Λ]).obj (op ((R((g)_*[ModuleCat.{u + 1} Λ])).obj N))).obj
      L).IsLE (q + (b + c) + 2 * dU + 2 * dV) :=
    _root_.DerivedCategory.isLE_of_iso_of_isLE
      (((RHom(X)[ModuleCat.{u + 1} Λ]).flip.obj L).mapIso
        ((rightDerivedLowerShriekIsoRightDerivedLowerStar _ g).app N).op).symm this
  exact _root_.DerivedCategory.TStructure.t.isLE_of_le _ (q + (b + c) + 2 * dU + 2 * dV) _
    (by lia)

/-- For `K ∈ Dctf(X_ét, Λ)`, `X` of finite type over a field and `Λ` finite, the derived hom
`RHom(K, -)` raises the upper bound of bounded complexes by a uniform amount: there is `B` such
that `RHom(K, L)` vanishes above `b + B` whenever `L` has homology in `[a, b]`.

By dévissage
(`AlgebraicGeometry.Etale.ctf_generated_by_rightDerivedLowerStar_rightDerivedLowerShriek`) it
suffices to treat the generators `Rg_* Rj_! P`
(`derivedHomBoundedAmplitude_rightDerivedLowerStar_rightDerivedLowerShriek`). -/
theorem derivedHomBoundedAmplitude_of_constructibleFiniteTor {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    derivedHomBoundedAmplitude Λ X K := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian aX }
  refine ctf_generated_by_rightDerivedLowerStar_rightDerivedLowerShriek Λ X _
    (fun str i Ubar j _ _ g _ _ _ P _ hP ↦ ?_) K hK
  have : TopologicalSpace.NoetherianSpace (str.domain i) :=
    (str.immersion i).isEmbedding.isInducing.noetherianSpace
  have : QuasiCompact j := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  exact derivedHomBoundedAmplitude_rightDerivedLowerStar_rightDerivedLowerShriek aX j g P hP

end Etale

end AlgebraicGeometry
