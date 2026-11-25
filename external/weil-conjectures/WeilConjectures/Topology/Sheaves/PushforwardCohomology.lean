/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Topology.Sheaves.LocallySurjective
public import WeilConjectures.CategoryTheory.Abelian.DimensionShifting
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.Topology.Sheaves.CechCriterion

/-!
# Cohomology of the pushforward of an abelian sheaf

Let `f : X ⟶ Y` be a continuous map. The pushforward `f_*` of abelian sheaves has an exact left
adjoint, so it preserves injective sheaves. Hence on every class of abelian sheaves on `X`
which is stable under the dimension shifting `0 → F → I → Q → 0` (with `I` injective) and on
which `f_*` preserves short exact sequences, the functors `F ↦ H^q(X, F)` and
`F ↦ H^q(Y, f_* F)` are effaceable δ-functors which agree in degree `0`, hence agree in all
degrees. This is the degenerate case of the Leray spectral sequence in which the higher direct
images vanish.

## Main definitions

- `TopCat.Sheaf.pushforwardAb`: the pushforward of abelian sheaves.

## Main statements

- `TopCat.Sheaf.injective_pushforwardAb_obj`: the pushforward of an injective sheaf is
  injective.
- `TopCat.Sheaf.shortExact_map_pushforward`: the pushforward of a short exact sequence which is
  surjective on the sections over the preimages of a basis is short exact.
- `TopCat.Sheaf.nonempty_functorH_iso_pushforwardAb`: `H^q(X, F) ≅ H^q(Y, f_* F)` on such a
  class of sheaves.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- The pushforward of abelian sheaves along a continuous map. -/
noncomputable abbrev pushforwardAb :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
      CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} :=
  (Opens.map f).sheafPushforwardContinuous AddCommGrpCat.{u} _ _

/-- The pushforward of an injective abelian sheaf is injective: the pushforward has an exact
left adjoint, the pullback. -/
lemma injective_pushforwardAb_obj
    (I : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) [Injective I] :
    Injective ((pushforwardAb f).obj I) := by
  have := lan_preservesFiniteLimits_of_flat (E := AddCommGrpCat.{u}) (Opens.map f)
  have : PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback (Opens.map f)
      AddCommGrpCat.{u} (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)) :=
    Functor.sheafPullbackConstruction.instPreservesFiniteLimitsSheafSheafPullback _ _ _ _
  exact Injective.injective_of_adjoint
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map f) AddCommGrpCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)) I

variable {f} in
/-- The pushforward of a short exact sequence of abelian sheaves is short exact as soon as it
is surjective on the sections over the preimages of the members of a basis. -/
lemma shortExact_map_pushforward
    {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) {B : Set (Opens Y)} (hB : Opens.IsBasis B)
    (h : ∀ V ∈ B, Function.Surjective (S.g.hom.app (op ((Opens.map f).obj V)))) :
    (S.map (pushforwardAb f)).ShortExact := by
  have hadj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map f)
    AddCommGrpCat.{u} (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
  have := hadj.rightAdjoint_preservesLimits
  have := hS.mono_f
  have hepi : Epi ((pushforwardAb f).map S.g) := by
    refine (CategoryTheory.Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u}
      ((pushforwardAb f).map S.g)).1 ?_
    refine (Presheaf.isLocallySurjective_iff ((pushforwardAb f).map S.g).hom).2
      fun W t y hy ↦ ?_
    obtain ⟨V, hV, hyV, hVW⟩ := Opens.isBasis_iff_nbhd.1 hB hy
    obtain ⟨s, hs⟩ := h V hV (S.X₃.obj.map (homOfLE ((Opens.map f).monotone
      (show V ≤ W from hVW))).op t)
    exact ⟨V, hVW, ⟨s, hs⟩, hyV⟩
  exact ShortComplex.ShortExact.mk' (hS.exact.map_of_mono_of_preservesKernel _ inferInstance
    inferInstance) (Functor.map_mono (pushforwardAb f) S.f) hepi

/-- `H⁰(Y, f_* F) = F(X) = H⁰(X, F)`. -/
noncomputable def functorHZeroIsoPushforwardAb :
    CategoryTheory.Sheaf.functorH.{u} (Opens.grothendieckTopology X) 0 ≅
      pushforwardAb f ⋙ CategoryTheory.Sheaf.functorH.{u} (Opens.grothendieckTopology Y) 0 :=
  CategoryTheory.Sheaf.functorHZeroIso.{u} _ isTerminalTop ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf _ _)
      ((evaluation _ _).mapIso (eqToIso (congrArg op (Opens.map_top f).symm))) ≪≫
    (Functor.isoWhiskerLeft (pushforwardAb f)
      (CategoryTheory.Sheaf.functorHZeroIso.{u} _ isTerminalTop)).symm

/-- **Cohomology of a pushforward.** Let `f : X ⟶ Y` be continuous and `P` a property of
abelian sheaves on `X`, stable under passing from `F` to the chosen injective sheaf `I` under
`F` and to the cokernel of `F ⟶ I`, such that the pushforward of a short exact sequence
`0 → F → G → H → 0` with `P F` is short exact. Then `H^q(X, F) ≅ H^q(Y, f_* F)`, naturally in
the sheaves `F` with `P F`. -/
theorem nonempty_functorH_iso_pushforwardAb
    (P : ObjectProperty (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
    (hP : ∀ F, P F → P (Injective.under F) ∧ P (cokernel (Injective.ι F)))
    (hf : ∀ S : ShortComplex
        (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}), S.ShortExact →
        P S.X₁ → (S.map (pushforwardAb f)).ShortExact) (q : ℕ) :
    Nonempty (P.ι ⋙ CategoryTheory.Sheaf.functorH.{u} (Opens.grothendieckTopology X) q ≅
      P.ι ⋙ pushforwardAb f ⋙
        CategoryTheory.Sheaf.functorH.{u} (Opens.grothendieckTopology Y) q) := by
  refine P.nonempty_iso_of_connecting hP
    (CategoryTheory.Sheaf.functorH.{u} (Opens.grothendieckTopology X))
    (fun q ↦ pushforwardAb f ⋙
      CategoryTheory.Sheaf.functorH.{u} (Opens.grothendieckTopology Y) q)
    (fun S hS _ q ↦ CategoryTheory.Sheaf.functorHδ hS q)
    (fun S hS h q ↦ CategoryTheory.Sheaf.functorHδ (hf S hS h) q) ?_ ?_ ?_ ?_ ?_ ?_ ?_ q
  · intro S₁ S₂ φ h₁ h₂ _ _ q
    exact CategoryTheory.Sheaf.functorHδ_naturality.{u} h₁ q h₂ φ
  · intro S₁ S₂ φ h₁ h₂ p₁ p₂ q
    exact CategoryTheory.Sheaf.functorHδ_naturality.{u} (hf _ h₁ p₁) q (hf _ h₂ p₂)
      ((pushforwardAb f).mapShortComplex.map φ)
  · intro S hS _ q x
    exact CategoryTheory.Sheaf.functorHδ_eq_zero_iff.{u} hS q x
  · intro S hS h q x
    exact CategoryTheory.Sheaf.functorHδ_eq_zero_iff.{u} (hf S hS h) q x
  · intro S hS _ q _
    exact CategoryTheory.Sheaf.functorHδ_surjective.{u} hS q
  · intro S hS h q _
    have : Injective (S.map (pushforwardAb f)).X₂ := injective_pushforwardAb_obj f S.X₂
    exact CategoryTheory.Sheaf.functorHδ_surjective.{u} (hf S hS h) q
  · exact Functor.isoWhiskerLeft P.ι (functorHZeroIsoPushforwardAb f)

end TopCat.Sheaf
