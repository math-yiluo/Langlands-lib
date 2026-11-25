/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.FilteredColimitStabilization
public import WeilConjectures.SixFunctors.Etale.Derived.Stalks.Support
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# Deligne's approximation by a constructible subsheaf

Let `X` be a Noetherian scheme, `Λ` a finite ring and `F` an étale sheaf of `Λ`-modules on `X`.
Let `hᵢ : Wᵢ ⟶ X` be finitely many morphisms from Noetherian schemes such that the pullbacks
`hᵢ^* F` are constructible. Then `F` has a constructible subsheaf `F₀` such that the stalks of
`F / F₀` vanish at all the points in the images of the `hᵢ`
(`AlgebraicGeometry.Etale.exists_mono_isConstructibleSheaf_isZero_sheafFiber_cokernel`).

Write `F` as the filtered union of its constructible subsheaves `F_S` (Stacks 03SA,
`AlgebraicGeometry.Etale.finsetSectionImage`). Pullback commutes with colimits and preserves
monomorphisms, so `hᵢ^* F` is the filtered union of the `hᵢ^* F_S`; being constructible on the
Noetherian `Wᵢ`, it equals one of them
(`AlgebraicGeometry.Etale.exists_epi_ι_app_of_isConstructibleSheaf`). A common stage `F_S` for
the finitely many `i` has `hᵢ^* (F / F_S) = 0`, so the stalks of `F / F_S` vanish on the images.

This is the spreading step of Deligne's proof of the finiteness of nearby cycles (SGA 4½,
[Th. finitude], proof of 3.2): for the geometric generic fibres `hᵢ` of the coordinates of
`𝔸ⁿ`, every non-closed point is in the image of some `hᵢ`, so `F / F₀` is supported at closed
points.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- **Deligne's approximation by a constructible subsheaf** (SGA 4½, [Th. finitude], proof of
3.2). Let `X` be Noetherian and `hᵢ : Wᵢ ⟶ X` finitely many morphisms from Noetherian schemes along
which the pullbacks of the étale sheaf `F` of modules over a finite ring are constructible. Then
`F` has a constructible subsheaf `F₀` whose cokernel has vanishing stalks at the points in the
images of the `hᵢ`. -/
theorem exists_mono_isConstructibleSheaf_isZero_sheafFiber_cokernel {X : Scheme.{u}}
    [IsNoetherian X] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {ι : Type*}
    [Finite ι] {W : ι → Scheme.{u}} [∀ i, IsNoetherian (W i)] (h : ∀ i, W i ⟶ X)
    (hF : ∀ i, IsConstructibleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) (h i)).obj F)) :
    ∃ (F₀ : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (a : F₀ ⟶ F), Mono a ∧
      IsConstructibleSheaf F₀ ∧ ∀ (i : ι) (w : W i),
        IsZero ((pointSmallEtale (X.algClosurePoint (h i w))).sheafFiber.obj (cokernel a)) := by
  classical
  let c := finsetSectionImageCocone F
  have key (i : ι) : ∃ S, Epi ((Etale.upperStar (ModuleCat.{u + 1} Λ) (h i)).map (c.ι.app S)) :=
    exists_epi_ι_app_of_isConstructibleSheaf
      (isColimitOfPreserves (Etale.upperStar (ModuleCat.{u + 1} Λ) (h i))
        (isColimitFinsetSectionImageCocone F))
      (fun S ↦ by dsimp; infer_instance) (hF i)
  choose S hS using key
  have := Fintype.ofFinite ι
  let T := Finset.univ.sup S
  refine ⟨_, c.ι.app T, inferInstance, inferInstance, fun i w ↦ ?_⟩
  let G := Etale.upperStar (ModuleCat.{u + 1} Λ) (h i)
  have hepi : Epi (G.map (c.ι.app T)) := by
    have hle : S i ⟶ T := homOfLE (Finset.le_sup (Finset.mem_univ i))
    have hS' := hS i
    rw [← c.w hle, G.map_comp] at hS'
    exact epi_of_epi (G.map ((finsetSectionImage F).map hle)) _
  have hzero : IsZero (G.obj (cokernel (c.ι.app T))) :=
    (isZero_cokernel_of_epi _).of_iso (PreservesCokernel.iso G _)
  let s := (W i).algClosurePoint w
  refine (isZero_sheafFiber_iff_of_apply_eq _ (s ≫ h i) _ ?_).mp
    (((pointSmallEtale s).sheafFiber.map_isZero hzero).of_iso
      ((Etale.upperStarCompSheafFiberIso _ (h i) s).app _).symm)
  simp [s]

end Etale

end AlgebraicGeometry
