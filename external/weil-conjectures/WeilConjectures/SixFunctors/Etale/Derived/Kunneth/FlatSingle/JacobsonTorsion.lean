/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.FiniteTypePushforward
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FlatSingle.Coefficients
public import WeilConjectures.SixFunctors.Finite.Exact
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal

/-!
# Sheaves killed by the Jacobson radical and finite direct images

Let `Λ` be a finite ring with Jacobson radical `J`. For a sheaf `F` of `Λ`-modules, the quotient
`F / J F` is the cokernel of `AlgebraicGeometry.Etale.smulDesc J F : ⨁_{x ∈ J} F ⟶ F`.

- `AlgebraicGeometry.Etale.exists_mono_biproduct_lowerStar_of_smul_eq_zero`: a constructible
  sheaf killed by `J` on a scheme of finite type over a field embeds into a finite sum of direct
  images along finite morphisms of constant sheaves with finite values killed by `J`.
- `AlgebraicGeometry.Etale.exists_retract_lowerStar_constantSheaf_of_smul_eq_zero`: for a finite
  morphism `π` and a finite module `M` killed by `J`, the sheaf `π_* M` is a retract of a finite
  sum of copies of `π_* Λ / J π_* Λ`.

These are the finite-pushforward steps of the proof of blueprint
`lemma-kunneth-field-coefficients--1`, for sheaves killed by `J` (blueprint
`lemma-finiteness-small-etale-topoi--3`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The map `⨁_{x ∈ I} F ⟶ F` given by the multiplications by the elements of a finite ideal; its
cokernel is `F / I F`. -/
noncomputable def smulDesc {C : Type*} [Category C] [Preadditive C] [Linear Λ C]
    [HasFiniteBiproducts C] (I : Ideal Λ) [Finite I] (F : C) :
    (⨁ fun _ : I ↦ F) ⟶ F :=
  biproduct.desc fun x ↦ (x : Λ) • 𝟙 F

section Functoriality

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D] [Linear Λ C]
  [Linear Λ D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]

/-- The map `AlgebraicGeometry.Etale.smulDesc` is natural. -/
lemma smulDesc_naturality (I : Ideal Λ) [Finite I] {A B : C} (f : A ⟶ B) :
    biproduct.map (fun _ ↦ f) ≫ smulDesc I B = smulDesc I A ≫ f := by
  ext x
  simp [smulDesc]

/-- A `Λ`-linear functor commutes with `AlgebraicGeometry.Etale.smulLift`. -/
lemma map_smulLift (Φ : C ⥤ D) [Φ.Additive] [Φ.Linear Λ] (I : Ideal Λ) [Finite I]
    (A : C) : Φ.map (smulLift I A) ≫ (Φ.mapBiproduct _).hom = smulLift I (Φ.obj A) := by
  ext x
  simp only [smulLift, Category.assoc, Functor.mapBiproduct_hom]
  erw [biproduct.lift_π, ← Φ.map_comp, biproduct.lift_π, biproduct.lift_π, Functor.map_smul,
    Φ.map_id]

/-- A `Λ`-linear functor commutes with `AlgebraicGeometry.Etale.smulDesc`. -/
lemma map_smulDesc (Φ : C ⥤ D) [Φ.Additive] [Φ.Linear Λ] (I : Ideal Λ) [Finite I]
    (A : C) : Φ.map (smulDesc I A) = (Φ.mapBiproduct _).hom ≫ smulDesc I (Φ.obj A) := by
  rw [← Iso.inv_comp_eq]
  ext x
  simp only [smulDesc, Functor.mapBiproduct_inv, biproduct.ι_desc_assoc, biproduct.ι_desc]
  rw [← Φ.map_comp, biproduct.ι_desc, Functor.map_smul, Φ.map_id]

/-- An isomorphism `A ≅ B` induces an isomorphism between the cokernels of
`AlgebraicGeometry.Etale.smulDesc`, i.e. `A / I A ≅ B / I B`. -/
noncomputable def cokernelSmulDescIsoOfIso [HasCokernels C] (I : Ideal Λ) [Finite I] {A B : C}
    (e : A ≅ B) : cokernel (smulDesc I A) ≅ cokernel (smulDesc I B) :=
  cokernel.mapIso _ _ (biproduct.mapIso fun _ ↦ e) e (smulDesc_naturality I e.hom).symm

/-- A `Λ`-linear functor preserving cokernels commutes with `F ↦ F / I F`. -/
noncomputable def mapCokernelSmulDescIso [HasCokernels C] [HasCokernels D] (Φ : C ⥤ D)
    [Φ.Additive] [Φ.Linear Λ] [PreservesFiniteColimits Φ] (I : Ideal Λ) [Finite I] (A : C) :
    Φ.obj (cokernel (smulDesc I A)) ≅ cokernel (smulDesc I (Φ.obj A)) :=
  PreservesCokernel.iso Φ _ ≪≫
    cokernel.mapIso _ _ (Φ.mapBiproduct _) (Iso.refl _)
      (by rw [Iso.refl_hom, Category.comp_id, map_smulDesc Φ I A])

/-- Let `Φ` be a `Λ`-linear functor preserving finite limits and `F` be killed by an ideal `I`.
Every morphism `F ⟶ Φ A` factors through `Φ` of the subobject `A[I]` of `A` killed by `I`. -/
lemma exists_comp_map_kernel_ι_smulLift [HasKernels C] [HasKernels D] (Φ : C ⥤ D)
    [Φ.Additive] [Φ.Linear Λ] [PreservesFiniteLimits Φ] (I : Ideal Λ) [Finite I] {F : D}
    (hF : ∀ x ∈ I, x • 𝟙 F = 0) {A : C} (g : F ⟶ Φ.obj A) :
    ∃ g' : F ⟶ Φ.obj (kernel (smulLift I A)), g' ≫ Φ.map (kernel.ι _) = g := by
  have hg : g ≫ Φ.map (smulLift I A) = 0 := by
    rw [← cancel_mono (Φ.mapBiproduct _).hom, Category.assoc, map_smulLift Φ, zero_comp]
    ext x
    simp only [smulLift, Category.assoc, zero_comp]
    erw [biproduct.lift_π]
    rw [Linear.comp_smul, Category.comp_id, ← Category.id_comp g, ← Linear.smul_comp, hF _ x.2,
      zero_comp]
  refine ⟨kernel.lift _ g hg ≫ inv (kernelComparison _ Φ), ?_⟩
  rw [← kernelComparison_comp_ι, Category.assoc, IsIso.inv_hom_id_assoc, kernel.lift_ι]

end Functoriality

variable (Λ) [Finite Λ]

-- Use the preadditive structure of `ModuleCat Λ` coming from `Abelian`, as the constructions for a
-- general abelian coefficient category do, so that the objects built here are syntactically
-- compatible with them.
attribute [local instance 10000] Abelian.toPreadditive SymmetricCategory.toBraidedCategory

/-- A finite `Λ`-module killed by the Jacobson radical `J` of `Λ` is a retract of a finite sum of
copies of `Λ / J`. -/
lemma ModuleCat.exists_retract_biproduct_cokernel_smulDesc (M : ModuleCat.{u + 1} Λ) [Finite M]
    (hM : ∀ x ∈ Ring.jacobson Λ, x • 𝟙 M = 0) :
    ∃ m : ℕ, Nonempty (Retract M
      (⨁ fun _ : Fin m ↦ cokernel (smulDesc (Ring.jacobson Λ) (ModuleCat.of Λ Λ)))) := by
  set J := Ring.jacobson Λ
  obtain ⟨n, ⟨eqv⟩⟩ := Finite.exists_equiv_fin M
  have hq (i : Fin n) : smulDesc J (ModuleCat.of Λ Λ) ≫
      ModuleCat.ofHom (LinearMap.toSpanSingleton Λ M (eqv.symm i)) = 0 := by
    refine biproduct.hom_ext' _ _ fun x ↦ ?_
    rw [smulDesc, biproduct.ι_desc_assoc, comp_zero, Linear.smul_comp, Category.id_comp,
      ← Category.comp_id (ModuleCat.ofHom _), ← Linear.comp_smul, hM _ x.2, comp_zero]
  let p : (⨁ fun _ : Fin n ↦ cokernel (smulDesc J (ModuleCat.of Λ Λ))) ⟶ M :=
    biproduct.desc fun i ↦ cokernel.desc _ _ (hq i)
  have hp : Function.Surjective p.hom := fun y ↦ by
    refine ⟨(biproduct.ι (fun _ : Fin n ↦ cokernel (smulDesc J (ModuleCat.of Λ Λ)))
      (eqv y)).hom
      ((cokernel.π (smulDesc J (ModuleCat.of Λ Λ))).hom 1), ?_⟩
    have h : cokernel.π (smulDesc J (ModuleCat.of Λ Λ)) ≫
        biproduct.ι (fun _ : Fin n ↦ cokernel (smulDesc J (ModuleCat.of Λ Λ))) (eqv y) ≫ p =
        ModuleCat.ofHom (LinearMap.toSpanSingleton Λ M (eqv.symm (eqv y))) := by
      simp [p]
    simpa using congr($h 1)
  have hN (x : Λ) (hx : x ∈ J) :
      x • 𝟙 (⨁ fun _ : Fin n ↦ cokernel (smulDesc J (ModuleCat.of Λ Λ))) = 0 := by
    have h1 : x • 𝟙 (ModuleCat.of Λ Λ) =
        biproduct.ι (fun _ : J ↦ ModuleCat.of Λ Λ) ⟨x, hx⟩ ≫ smulDesc J _ := by
      simp [smulDesc]
    refine biproduct.hom_ext' _ _ fun i ↦ ?_
    rw [← cancel_epi (cokernel.π _), comp_zero, comp_zero, Linear.comp_smul, Linear.comp_smul,
      Category.comp_id, ← Category.id_comp (cokernel.π _ ≫ _), ← Linear.smul_comp, h1,
      Category.assoc, cokernel.condition_assoc, zero_comp, comp_zero]
  have hN' : Module.IsTorsionBySet Λ
      (ModuleCat.carrier (⨁ fun _ : Fin n ↦ cokernel (smulDesc J (ModuleCat.of Λ Λ)))) J :=
    fun y x ↦ by simpa using congr($(hN x.1 x.2) y)
  let := hN'.module
  have : IsSemisimpleModule Λ
      (ModuleCat.carrier (⨁ fun _ : Fin n ↦ cokernel (smulDesc J (ModuleCat.of Λ Λ)))) :=
    hN'.isSemisimpleModule_iff.1 inferInstance
  obtain ⟨s, hs⟩ := IsSemisimpleModule.lifting_property p.hom hp LinearMap.id
  exact ⟨n, ⟨{ i := ModuleCat.ofHom s, r := p, retract := by ext y; exact congr($hs y) }⟩⟩

/-- A constructible sheaf killed by the Jacobson radical `J` of `Λ`, on a scheme of finite type
over a field, embeds into a finite sum of direct images along finite morphisms of constant sheaves
with finite values killed by `J` (blueprint `lemma-finiteness-small-etale-topoi--3`
for sheaves killed by `J`, used in the proof of blueprint `lemma-kunneth-field-coefficients--1`). -/
theorem exists_mono_biproduct_lowerStar_of_smul_eq_zero {k : Type u} [Field k]
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F]
    (hF : ∀ x ∈ Ring.jacobson Λ, x • 𝟙 F = 0) :
    ∃ (r : ℕ) (Y : Fin r → Scheme.{u}) (h : ∀ i, Y i ⟶ X) (_ : ∀ i, IsFinite (h i))
      (M : Fin r → ModuleCat.{u + 1} Λ) (_ : ∀ i, Finite (M i))
      (_ : ∀ i, ∀ x ∈ Ring.jacobson Λ, x • 𝟙 (M i) = 0)
      (φ : F ⟶ ⨁ fun i ↦ ((h i)_*[ModuleCat.{u + 1} Λ]).obj
        ((constantSheaf (Y i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M i))), Mono φ := by
  obtain ⟨r, Y, h, hh, M, hM, φ, hφ⟩ :=
    exists_mono_biproduct_lowerStar_of_locallyOfFiniteType Λ aX F
  let Φ (i : Fin r) := constantSheaf (Y i).smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
    (h i)_*[ModuleCat.{u + 1} Λ]
  choose g hg using fun i ↦ exists_comp_map_kernel_ι_smulLift (Φ i) (Ring.jacobson Λ) hF
    (φ ≫ biproduct.π _ i)
  refine ⟨r, Y, h, hh, fun i ↦ kernel (smulLift (Ring.jacobson Λ) (M i)), fun i ↦ ?_,
    fun i _ hx ↦ smul_id_kernel_smulLift _ _ hx, biproduct.lift g, ?_⟩
  · exact Finite.of_injective _
      ((ModuleCat.mono_iff_injective (kernel.ι (smulLift (Ring.jacobson Λ) (M i)))).1
        inferInstance)
  · have hfac : biproduct.lift g ≫ biproduct.map (fun i ↦ (Φ i).map (kernel.ι _)) = φ := by
      refine biproduct.hom_ext _ _ fun i ↦ ?_
      simp only [biproduct.lift_map, biproduct.lift_π, hg]
      rfl
    exact mono_of_mono_fac hfac

/-- For a finite morphism `π` and a finite `Λ`-module `M` killed by the Jacobson radical `J`, the
sheaf `π_* M` is a retract of a finite sum of copies of `π_* Λ / J π_* Λ`
(used in the proof of blueprint `lemma-kunneth-field-coefficients--1`). -/
theorem exists_retract_lowerStar_constantSheaf_of_smul_eq_zero {X Y : Scheme.{u}} (π : Y ⟶ X)
    [IsFinite π] (M : ModuleCat.{u + 1} Λ) [Finite M]
    (hM : ∀ x ∈ Ring.jacobson Λ, x • 𝟙 M = 0) :
    ∃ m : ℕ, Nonempty (Retract
      ((π)_*[ModuleCat.{u + 1} Λ].obj
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))
      (⨁ fun _ : Fin m ↦ cokernel
        (smulDesc (Ring.jacobson Λ) ((π)_*[ModuleCat.{u + 1} Λ].obj (𝟙_ _))))) := by
  obtain ⟨m, ⟨ρ⟩⟩ := ModuleCat.exists_retract_biproduct_cokernel_smulDesc Λ M hM
  let Φ := constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
    (π)_*[ModuleCat.{u + 1} Λ]
  let e : Φ.obj (cokernel (smulDesc (Ring.jacobson Λ) (ModuleCat.of Λ Λ))) ≅
      cokernel (smulDesc (Ring.jacobson Λ) ((π)_*[ModuleCat.{u + 1} Λ].obj (𝟙_ _))) :=
    mapCokernelSmulDescIso Φ (Ring.jacobson Λ) _ ≪≫ cokernelSmulDescIsoOfIso _
      ((π)_*[ModuleCat.{u + 1} Λ].mapIso
        (Functor.Monoidal.εIso (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))).symm)
  exact ⟨m, ⟨(ρ.map Φ).trans
    (Φ.mapBiproduct _ ≪≫ biproduct.mapIso fun _ ↦ e).retract⟩⟩

end Etale

end AlgebraicGeometry
