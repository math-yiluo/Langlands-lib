/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.SimpleModule.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeResidue
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude

/-!
# The residue test for Tor amplitude on the pro-étale site

Let `Λ` be a commutative ring and `ϖ ∈ Λ` a nilpotent element such that `κ = Λ ⧸ (ϖ)` is a
field (the finite coefficient stage `A_{E,n} = 𝒪_E / ϖⁿ`, with residue field `κ`). For a scheme
`T`, an object `K` of `D(T_proét, Λ)` has Tor amplitude in `[a, b]` if and only if
`K ⊗ᴸ κ_T` has homology concentrated in `[a, b]`, where `κ_T` is the constant sheaf with value
`κ` (`AlgebraicGeometry.ProEtale.DerivedCategory.torAmplitudeIn_iff_homologyConcentratedIn_tensor`,
blueprint `lemma-bounds-finite-reductions--2`).

This is the categorical residue test
`DerivedCategory.torAmplitudeIn_iff_homologyConcentratedIn_tensor_singleFunctor`, whose two
inputs are proved here for sheaves of `Λ`-modules on any essentially small site:

- `CategoryTheory.Sheaf.constantSheafQuotientIsoCokernel`: the constant sheaf `κ` is the
  cokernel of `ϖ` on the unit sheaf;
- `CategoryTheory.Sheaf.mono_whiskerRight_of_smul_id_eq_zero`: tensoring with any sheaf
  preserves monomorphisms whose target is killed by `ϖ`. Indeed, sectionwise such a
  monomorphism is a split monomorphism of `Λ`-modules
  (`ModuleCat.isSplitMono_of_smul_id_eq_zero`: modules over the field `κ` are semisimple), so
  it stays a monomorphism after tensoring the sections, and sheafification preserves
  monomorphisms.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace ModuleCat

/-- A monomorphism of `Λ`-modules whose target is killed by `r` is split when `Λ ⧸ (r)` is a
field: the target is a semisimple module, being a vector space over `Λ ⧸ (r)`. -/
lemma isSplitMono_of_smul_id_eq_zero {Λ : Type*} [CommRing Λ] (r : Λ)
    [(Ideal.span {r}).IsMaximal] {M N : ModuleCat Λ} (f : M ⟶ N) [Mono f]
    (hN : r • 𝟙 N = 0) : IsSplitMono f := by
  have hN' : Module.IsTorsionBySet Λ N (Ideal.span {r}) :=
    (Module.isTorsionBySet_span_singleton_iff r).2 fun x ↦ by
      simpa using congr($hN x)
  let := hN'.module
  let : Field (Λ ⧸ Ideal.span {r}) := Ideal.Quotient.field _
  have : IsSemisimpleModule Λ N := hN'.isSemisimpleModule_iff.1 inferInstance
  obtain ⟨g, hg⟩ := IsSemisimpleModule.extension_property f.hom
    ((ModuleCat.mono_iff_injective f).1 inferInstance) LinearMap.id
  exact ⟨⟨ModuleCat.ofHom g, by ext x; exact congr($hg x)⟩⟩

/-- The quotient `Λ ⧸ (r)` is the cokernel of multiplication by `r` on `Λ`. -/
noncomputable def quotientSpanSingletonIsoCokernel {Λ : Type*} [CommRing Λ] (r : Λ) :
    ModuleCat.of Λ (Λ ⧸ Ideal.span {r}) ≅ cokernel (r • 𝟙 (ModuleCat.of Λ Λ)) :=
  (Submodule.quotEquivOfEq (Ideal.span {r}) (r • 𝟙 (ModuleCat.of Λ Λ)).hom.range (by
    ext x
    simp [Ideal.mem_span_singleton', eq_comm, mul_comm])).toModuleIso ≪≫
    (ModuleCat.cokernelIsoRangeQuotient _).symm

end ModuleCat

namespace CategoryTheory.Sheaf

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C} {Λ : Type (u + 1)} [CommRing Λ]

/-- Let `Λ ⧸ (r)` be a field. For sheaves of `Λ`-modules on an essentially small site, tensoring
with any sheaf `F` preserves monomorphisms `f` whose target is killed by `r`.

Sectionwise `f` is a split monomorphism (`ModuleCat.isSplitMono_of_smul_id_eq_zero`), so the
presheaf tensor product `f ▷ F` is a monomorphism, and so is its sheafification. -/
lemma mono_whiskerRight_of_smul_id_eq_zero (r : Λ) [(Ideal.span {r}).IsMaximal]
    {X Y : Sheaf J (ModuleCat.{u + 1} Λ)} (f : X ⟶ Y) [Mono f] (hY : r • 𝟙 Y = 0)
    (F : Sheaf J (ModuleCat.{u + 1} Λ)) : Mono (f ▷ F) := by
  have : Mono f.hom := inferInstanceAs (Mono ((sheafToPresheaf J _).map f))
  have (U : Cᵒᵖ) : Mono ((f.hom ▷ F.obj).app U) := by
    have : IsSplitMono (f.hom.app U) :=
      ModuleCat.isSplitMono_of_smul_id_eq_zero r _ congr(($hY).hom.app U)
    exact inferInstanceAs (Mono ((tensorRight _).map (f.hom.app U)))
  have : Mono (f.hom ▷ F.obj) := NatTrans.mono_of_mono_app _
  have : Mono ((sheafToPresheaf J _ ⋙ tensorRight F.obj ⋙ presheafToSheaf J _).map f) :=
    inferInstanceAs (Mono ((presheafToSheaf J _).map (f.hom ▷ F.obj)))
  change Mono ((tensorRight F).map f)
  rw [← NatIso.naturality_2 (Sheaf.tensorRightIso F) f]
  infer_instance

variable (J) in
/-- The constant sheaf with value `Λ ⧸ (r)` is the cokernel of `r` on the unit sheaf: the
constant sheaf functor is right exact and sends `Λ` to the unit. -/
noncomputable def constantSheafQuotientIsoCokernel (r : Λ) :
    (constantSheaf J (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ (Λ ⧸ Ideal.span {r})) ≅
      cokernel (r • 𝟙 (𝟙_ (Sheaf J (ModuleCat.{u + 1} Λ)))) :=
  have : PreservesFiniteColimits (constantSheaf J (ModuleCat.{u + 1} Λ)) :=
    comp_preservesFiniteColimits (Functor.const _) (presheafToSheaf J _)
  (constantSheaf J _).mapIso (ModuleCat.quotientSpanSingletonIsoCokernel r) ≪≫
    PreservesCokernel.iso (constantSheaf J _) _ ≪≫
    cokernelIsoOfEq (f := (constantSheaf J _).map (r • 𝟙 (ModuleCat.of Λ Λ)))
      (g := r • 𝟙 _) (by rw [Functor.map_smul, Functor.map_id]) ≪≫
    cokernel.mapIso _ _ (Functor.Monoidal.εIso (presheafToSheaf J _)).symm
      (Functor.Monoidal.εIso (presheafToSheaf J _)).symm
      (by rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id])

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.ProEtale.DerivedCategory

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- Blueprint `lemma-bounds-finite-reductions--2`: The residue test on the pro-étale site.

Let `ϖ ∈ Λ` be nilpotent with `Λ ⧸ (ϖ)` a field (for instance `Λ = A_{E,n} = 𝒪_E / ϖⁿ`), and let
`κ_T` be the constant pro-étale sheaf on `T` with value the `Λ`-module `κ = Λ ⧸ (ϖ)`. Then
`K ∈ D(T_proét, Λ)` has Tor amplitude in `[a, b]` if and only if `K ⊗ᴸ κ_T` has homology
concentrated in `[a, b]`. The blueprint states this for bounded constructible `K`; it holds for
every `K`, and needs neither the finiteness of `Λ` nor any hypothesis on `T`.

This is `DerivedCategory.torAmplitudeIn_iff_homologyConcentratedIn_tensor_singleFunctor`, with
`κ_T ≅ 𝟙 / ϖ` (`CategoryTheory.Sheaf.constantSheafQuotientIsoCokernel`) and the flatness of
sheaves of `κ`-modules (`CategoryTheory.Sheaf.mono_whiskerRight_of_smul_id_eq_zero`). -/
theorem torAmplitudeIn_iff_homologyConcentratedIn_tensor (ϖ : Λ) (hϖ : IsNilpotent ϖ)
    [(Ideal.span {ϖ}).IsMaximal] {T : Scheme.{u}} (a b : ℤ)
    (K : _root_.DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} Λ))) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) T a b K ↔
      _root_.DerivedCategory.homologyConcentratedIn a b
        (K ⊗ (_root_.DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf (ProEt.topology T) (ModuleCat.{u + 1} Λ)).obj
            (ModuleCat.of Λ (Λ ⧸ Ideal.span {ϖ})))) :=
  _root_.DerivedCategory.torAmplitudeIn_iff_homologyConcentratedIn_tensor_singleFunctor
    (C := Sheaf (ProEt.topology T) (ModuleCat.{u + 1} Λ)) (R := Λ) ϖ hϖ
    (Sheaf.constantSheafQuotientIsoCokernel (ProEt.topology T) ϖ)
    (fun F _ _ _ f _ _ hY ↦ Sheaf.mono_whiskerRight_of_smul_id_eq_zero ϖ f hY F) a b K

end AlgebraicGeometry.ProEtale.DerivedCategory
