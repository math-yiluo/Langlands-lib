/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.TorsionFreeResolution
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushResidueIsoReduction

/-!
# Torsion-free acyclic resolutions of complexes of module objects

Let `C` be a closed symmetric monoidal Grothendieck abelian category with functorial flat
resolutions, `R : C` a commutative algebra object, `r` an endomorphism of the regular `R`-module,
and `ι : R ⟶ F` a monomorphism of `R`-modules such that `F ⊗_R -` preserves monomorphisms and `r`
acts on `F` by an epimorphism (in the application: `ι : 𝒪_{E,X} ⟶ E_X` and `r = ϖ`).

We show (`CategoryTheory.Mod.exists_iso_Q_obj_mono_regularEndSMul`) that every bounded below
object `K ≥ n` of `D(Mod_R)` is represented by a complex `J ≥ n - 1` on whose terms `r` acts
injectively (`Mod.regularEndSMul`) and whose terms are acyclic for every left exact right adjoint
`G` whose left adjoint `L` preserves monomorphisms and such that every object is a quotient of an
object `M` with `ι ▷ L M` a monomorphism (see `exists_epi_mono_whiskerRight_obj` for a criterion).
The complex `J` is `CochainComplex.torsionFreeResolution ι I` for a bounded below injective
resolution `I` of `K`.
-/

@[expose] public section

universe v u v' u'

open CategoryTheory MonoidalCategory MonoidalClosed Limits

attribute [local instance] Bimod.monoidalCategory

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  {R : C} [MonObj R] [IsCommMonObj R]

omit [MonoidalPreadditive C] in
lemma regularEndSMul_eq_unitEndSMul (r : 𝟙_ (Mod C R) ⟶ 𝟙_ (Mod C R)) (M : Mod C R) :
    regularEndSMul r M = unitEndSMul r M := rfl

section Comap

variable {S : C} [MonObj S] [IsCommMonObj S] (φ : R ⟶ S) [IsMonHom φ]

omit [MonoidalPreadditive C] [IsCommMonObj R] [IsCommMonObj S] [SymmetricCategory C]
  [MonoidalClosed C] [IsGrothendieckAbelian.{v} C] in
/-- The `R`-linear map `R ⟶ φ^* S` is a monomorphism if `φ` is. -/
lemma mono_regularToComapRegular [Mono φ] : Mono (regularToComapRegular φ) :=
  (forget R).mono_of_mono_map (by simpa using (inferInstance : Mono φ))

/-- Tensoring with `φ^* S` preserves monomorphisms if the extension of scalars along `φ` is left
exact (`S` is flat over `R`): both agree after forgetting to `C`. -/
lemma preservesMonomorphisms_tensorLeft_comap_regular [PreservesFiniteLimits (extendScalars φ)] :
    (tensorLeft ((comap φ).obj (regular S))).PreservesMonomorphisms where
  preserves {M N} g _ := by
    refine (forget R).mono_of_mono_map ?_
    have : Mono ((forget S).map ((extendScalars φ).map g)) :=
      (forget S).map_mono ((extendScalars φ).map g)
    have h := (extendForgetTensorIso φ).hom.naturality g
    dsimp only [Functor.comp_map] at h
    have : Mono ((extendForgetTensorIso φ).hom.app M ≫
        (forget R).map ((tensorLeft ((comap φ).obj (regular S))).map g)) := by
      rw [← h]
      infer_instance
    simpa only [IsIso.inv_hom_id_assoc] using
      mono_comp (inv ((extendForgetTensorIso φ).hom.app M)) ((extendForgetTensorIso φ).hom.app M ≫
        (forget R).map ((tensorLeft ((comap φ).obj (regular S))).map g))

end Comap

variable [Abelian.HasFunctorialFlatResolution C] [HasDerivedCategory (Mod C R)]
  {F : Mod C R} (ι : 𝟙_ (Mod C R) ⟶ F) [Mono ι] [(tensorLeft F).PreservesMonomorphisms]
  (r : 𝟙_ (Mod C R) ⟶ 𝟙_ (Mod C R)) [Epi (regularEndSMul r F)]

/-- **Torsion-free acyclic resolutions**: every bounded below object `K ≥ n` of the derived
category of `R`-modules is represented by a complex `J ≥ n - 1` on whose terms `r` acts
injectively, and whose terms are `G`-acyclic for every left exact right adjoint `G` whose left
adjoint `L` preserves monomorphisms and such that every object is a quotient of an object `M`
with `ι ▷ L M` a monomorphism. -/
theorem exists_iso_Q_obj_mono_regularEndSMul (K : DerivedCategory (Mod C R)) (n : ℤ)
    [K.IsGE n] :
    ∃ (J : CochainComplex (Mod C R) ℤ), Nonempty (K ≅ DerivedCategory.Q.obj J) ∧
      J.IsStrictlyGE (n - 1) ∧ (∀ k, Mono (regularEndSMul r (J.X k))) ∧
      ∀ {D' : Type u'} [Category.{v'} D'] [Abelian D'] {L : D' ⥤ Mod C R}
        {G : Mod C R ⥤ D'} [G.Additive] [PreservesFiniteLimits G] (_ : L ⊣ G)
        [L.PreservesMonomorphisms]
        (_ : ∀ Y : D', ∃ (M : D') (π : M ⟶ Y), Epi π ∧ Mono (ι ▷ L.obj M)) (k : ℤ),
        G.rightAcyclic (J.X k) := by
  have hgen := exists_epi_mono_whiskerRight ι
  obtain ⟨I, hI, _, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_torsionFreeResolution ι hgen K n
  have : Epi (unitEndSMul r F) := inferInstanceAs (Epi (regularEndSMul r F))
  exact ⟨_, ⟨e⟩, CochainComplex.isStrictlyGE_torsionFreeResolution ι I n,
    CochainComplex.mono_unitEndSMul_torsionFreeResolution_X ι I r,
    fun adj _ hL k ↦ CochainComplex.rightAcyclic_torsionFreeResolution_X ι I hI hgen adj hL k⟩

end CategoryTheory.Mod
