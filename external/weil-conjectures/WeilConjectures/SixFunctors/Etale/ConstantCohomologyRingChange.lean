/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctor
public import WeilConjectures.SixFunctors.Etale.ConstantCohomologyExt

/-!
# Change of coefficient ring for the cohomology of the constant étale sheaf

Let `φ : Λ' ⟶ Λ` be a ring homomorphism and `X` a quasi-compact quasi-separated scheme. The
cohomology `Hⁿ(X_ét, Λ) = Extⁿ(Λ_X, Λ_X)` of the constant sheaf, computed with étale sheaves of
`Λ`-modules, is a graded ring for the Yoneda product, and `φ` induces a map
`φ_* : Extⁿ(Λ'_X, Λ'_X) ⟶ Extⁿ(Λ_X, Λ_X)` (`AlgebraicGeometry.Etale.extRingChange`): on the
underlying abelian cohomology groups `Hⁿ(X_ét, Λ') ⟶ Hⁿ(X_ét, Λ)` it is induced by the map of
abelian sheaves `Λ'_X ⟶ Λ_X` (`AlgebraicGeometry.Etale.mapExtComp_extRingChange`).

The map `φ_*` is multiplicative for the Yoneda products
(`AlgebraicGeometry.Etale.extRingChange_comp`). The proof goes through the restriction of
scalars `φ^* : Sh(X_ét, Λ) ⥤ Sh(X_ét, Λ')`, an exact functor: `φ_* z` is the unique class `w`
with `ψ ∘ φ^* w = z ∘ ψ` in `Extⁿ(Λ'_X, φ^* Λ_X)`, where `ψ : Λ'_X ⟶ φ^* Λ_X` is the map of
constant sheaves (`AlgebraicGeometry.Etale.mk₀_comp_mapExactFunctor_extRingChange`), and this
characterization is compatible with composition.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Abelian

namespace AlgebraicGeometry.Etale

variable {Λ' Λ : Type (u + 1)} [CommRing Λ'] [CommRing Λ] (φ : Λ' →+* Λ) (X : Scheme.{u})

/-- Restriction of scalars along `φ : Λ' ⟶ Λ`, for étale sheaves of modules. -/
noncomputable abbrev sheafRestrictScalars :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ') :=
  sheafCompose X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} φ)

instance : (sheafRestrictScalars φ X).Additive where
  map_add {_ _ _ _} := by
    apply Sheaf.hom_ext
    ext U x
    rfl

instance : PreservesFiniteLimits (sheafRestrictScalars φ X) := by
  have : PreservesLimitsOfSize.{u + 1, u + 1} (ModuleCat.restrictScalars.{u + 1} φ) :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1} φ).rightAdjoint_preservesLimits
  have : PreservesFiniteLimits (sheafRestrictScalars φ X ⋙
      sheafToPresheaf _ (ModuleCat.{u + 1} Λ')) :=
    inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf _ _ ⋙
      (Functor.whiskeringRight X.Etaleᵒᵖ _ _).obj (ModuleCat.restrictScalars.{u + 1} φ)))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)

instance : PreservesFiniteColimits (sheafRestrictScalars φ X) := by
  have hadj := ModuleCat.restrictCoextendScalarsAdj.{u + 1} φ
  have : PreservesLimitsOfSize.{u, u + 1} (ModuleCat.coextendScalars.{u + 1} φ) :=
    hadj.rightAdjoint_preservesLimits
  have : X.smallEtaleTopology.HasSheafCompose (ModuleCat.coextendScalars.{u + 1} φ) :=
    hasSheafCompose_of_preservesLimitsOfSize _
  have := (Sheaf.adjunction X.smallEtaleTopology hadj).isLeftAdjoint
  exact preservesFiniteColimits_of_natIso
    (sheafToPresheafCompWhiskeringRightCompPresheafToSheafIso _ _)

/-- Forgetting the `Λ'`-module structure of the restriction of scalars of a sheaf of
`Λ`-modules is forgetting its `Λ`-module structure. -/
noncomputable def sheafRestrictScalarsCompSheafForget₂Iso :
    sheafRestrictScalars φ X ⋙ sheafForget₂ Λ' X ≅ sheafForget₂ Λ X :=
  Iso.refl _

/-- The map of constant sheaves `ψ : Λ'_X ⟶ φ^* Λ_X` induced by `φ`: it sends the section `1`
to the section `1`. -/
noncomputable def constantRingMap :
    Sheaf.constantRing X.smallEtaleTopology Λ' ⟶
      (sheafRestrictScalars φ X).obj (Sheaf.constantRing X.smallEtaleTopology Λ) :=
  (Sheaf.constantRingHomEquiv _ (terminalEtaleIsTerminal X) Λ' _).symm
    (Sheaf.constantRingHomEquiv _ (terminalEtaleIsTerminal X) Λ _ (𝟙 _))

/-- The map of underlying abelian sheaves `Λ'_X ⟶ Λ_X` induced by `φ`. -/
noncomputable def constantRingForgetMap :
    (sheafForget₂ Λ' X).obj (Sheaf.constantRing X.smallEtaleTopology Λ') ⟶
      (sheafForget₂ Λ X).obj (Sheaf.constantRing X.smallEtaleTopology Λ) :=
  (sheafForget₂ Λ' X).map (constantRingMap φ X) ≫
    (sheafRestrictScalarsCompSheafForget₂Iso φ X).hom.app _

/-- The map `Λ'_X ⟶ Λ_X` of underlying abelian sheaves sends the class of `1` to the class of
`1`. -/
lemma constantIntToRing_comp_constantRingForgetMap :
    Sheaf.constantIntToRing X.smallEtaleTopology (terminalEtaleIsTerminal X) Λ' ≫
        constantRingForgetMap φ X =
      Sheaf.constantIntToRing X.smallEtaleTopology (terminalEtaleIsTerminal X) Λ := by
  refine (Sheaf.constantHomEquiv (terminalEtaleIsTerminal X) _).injective ?_
  rw [Sheaf.constantHomEquiv_comp, Sheaf.constantIntToRing, Sheaf.constantIntToRing]
  erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have h := Sheaf.constantRingHomEquiv_comp X.smallEtaleTopology (terminalEtaleIsTerminal X) Λ'
    (𝟙 _) (constantRingMap φ X)
  rw [Category.id_comp, constantRingMap] at h
  exact h.symm.trans (Equiv.apply_symm_apply _ _)

variable [CompactSpace X] [QuasiSeparatedSpace X]

/-- The map `φ_* : Extⁿ(Λ'_X, Λ'_X) ⟶ Extⁿ(Λ_X, Λ_X)` induced by a ring homomorphism
`φ : Λ' ⟶ Λ`: on abelian cohomology `Hⁿ(X_ét, Λ') ⟶ Hⁿ(X_ét, Λ)` it is induced by the map of
sheaves `Λ'_X ⟶ Λ_X` (`AlgebraicGeometry.Etale.mapExtComp_extRingChange`). -/
noncomputable def extRingChange (n : ℕ) :
    Ext (Sheaf.constantRing X.smallEtaleTopology Λ') (Sheaf.constantRing X.smallEtaleTopology Λ')
        n →+
      Ext (Sheaf.constantRing X.smallEtaleTopology Λ)
        (Sheaf.constantRing X.smallEtaleTopology Λ) n :=
  AddMonoidHom.mk' (fun z ↦ (AddEquiv.ofBijective _
    (bijective_mapExtComp_constantIntToRing Λ X (Sheaf.constantRing X.smallEtaleTopology Λ)
      n)).symm
      (((sheafForget₂ Λ' X).mapExtComp
        (Sheaf.constantIntToRing X.smallEtaleTopology (terminalEtaleIsTerminal X) Λ') _ n
          z).comp (Ext.mk₀ (constantRingForgetMap φ X)) (add_zero n))) fun z z' ↦ by
    rw [map_add, Ext.add_comp, map_add]

/-- On abelian cohomology, `φ_*` is induced by the map of sheaves `Λ'_X ⟶ Λ_X`. -/
lemma mapExtComp_extRingChange (n : ℕ)
    (z : Ext (Sheaf.constantRing X.smallEtaleTopology Λ')
      (Sheaf.constantRing X.smallEtaleTopology Λ') n) :
    (sheafForget₂ Λ X).mapExtComp
        (Sheaf.constantIntToRing X.smallEtaleTopology (terminalEtaleIsTerminal X) Λ) _ n
        (extRingChange φ X n z) =
      ((sheafForget₂ Λ' X).mapExtComp
        (Sheaf.constantIntToRing X.smallEtaleTopology (terminalEtaleIsTerminal X) Λ') _ n
          z).comp (Ext.mk₀ (constantRingForgetMap φ X)) (add_zero n) :=
  (AddEquiv.ofBijective _ (bijective_mapExtComp_constantIntToRing Λ X
    (Sheaf.constantRing X.smallEtaleTopology Λ) n)).apply_symm_apply _

omit [CompactSpace X] [QuasiSeparatedSpace X] in
/-- Pushing `ψ ∘ φ^* w` to abelian cohomology gives the abelian cohomology class of `w`, up to
the identification `sheafRestrictScalarsCompSheafForget₂Iso`. -/
lemma mapExtComp_mk₀_constantRingMap_comp_mapExactFunctor (n : ℕ)
    (w : Ext (Sheaf.constantRing X.smallEtaleTopology Λ)
      (Sheaf.constantRing X.smallEtaleTopology Λ) n) :
    (sheafForget₂ Λ' X).mapExtComp
        (Sheaf.constantIntToRing X.smallEtaleTopology (terminalEtaleIsTerminal X) Λ') _ n
        ((Ext.mk₀ (constantRingMap φ X)).comp
          (w.mapExactFunctor (sheafRestrictScalars φ X)) (zero_add n)) =
      ((sheafForget₂ Λ X).mapExtComp
        (Sheaf.constantIntToRing X.smallEtaleTopology (terminalEtaleIsTerminal X) Λ) _ n w).comp
        (Ext.mk₀ ((sheafRestrictScalarsCompSheafForget₂Iso φ X).inv.app _)) (add_zero n) := by
  rw [Functor.mapExtComp_apply, Functor.mapExtComp_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_mapExactFunctor,
    Ext.mapExactFunctor_eq_of_iso (sheafRestrictScalarsCompSheafForget₂Iso φ X).symm,
    ← constantIntToRing_comp_constantRingForgetMap φ X, constantRingForgetMap]
  simp only [Iso.symm_inv, Iso.symm_hom, Ext.mk₀_comp_mk₀_assoc, Ext.comp_assoc_of_third_deg_zero]

/-- `w ↦ ψ ∘ φ^* w` is injective on `Extⁿ(Λ_X, Λ_X)`. -/
lemma injective_mk₀_constantRingMap_comp_mapExactFunctor (n : ℕ) :
    Function.Injective fun w : Ext (Sheaf.constantRing X.smallEtaleTopology Λ)
        (Sheaf.constantRing X.smallEtaleTopology Λ) n ↦
      (Ext.mk₀ (constantRingMap φ X)).comp
        (w.mapExactFunctor (sheafRestrictScalars φ X)) (zero_add n) := by
  intro w₁ w₂ h
  have h' := congrArg (fun e ↦ (e.comp (Ext.mk₀ ((sheafRestrictScalarsCompSheafForget₂Iso φ
    X).hom.app (Sheaf.constantRing X.smallEtaleTopology Λ))) (add_zero n)))
      (congrArg ((sheafForget₂ Λ' X).mapExtComp
        (Sheaf.constantIntToRing X.smallEtaleTopology (terminalEtaleIsTerminal X) Λ') _ n) h)
  simp only [mapExtComp_mk₀_constantRingMap_comp_mapExactFunctor,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Iso.inv_hom_id_app, Ext.comp_mk₀_id] at h'
  exact (bijective_mapExtComp_constantIntToRing Λ X _ n).1 h'

/-- `φ_* z` is the unique class `w` with `ψ ∘ φ^* w = z ∘ ψ` in `Extⁿ(Λ'_X, φ^* Λ_X)`. -/
lemma mk₀_comp_mapExactFunctor_extRingChange (n : ℕ)
    (z : Ext (Sheaf.constantRing X.smallEtaleTopology Λ')
      (Sheaf.constantRing X.smallEtaleTopology Λ') n) :
    (Ext.mk₀ (constantRingMap φ X)).comp
        ((extRingChange φ X n z).mapExactFunctor (sheafRestrictScalars φ X)) (zero_add n) =
      z.comp (Ext.mk₀ (constantRingMap φ X)) (add_zero n) := by
  apply (bijective_mapExtComp_constantIntToRing Λ' X _ n).1
  rw [mapExtComp_mk₀_constantRingMap_comp_mapExactFunctor, mapExtComp_extRingChange,
    Functor.mapExtComp_comp_mk₀, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
    constantRingForgetMap, Category.assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id]

/-- **`φ_*` is multiplicative for the Yoneda product.** -/
theorem extRingChange_comp {a b c : ℕ} (h : a + b = c)
    (z : Ext (Sheaf.constantRing X.smallEtaleTopology Λ')
      (Sheaf.constantRing X.smallEtaleTopology Λ') a)
    (z' : Ext (Sheaf.constantRing X.smallEtaleTopology Λ')
      (Sheaf.constantRing X.smallEtaleTopology Λ') b) :
    extRingChange φ X c (z.comp z' h) =
      (extRingChange φ X a z).comp (extRingChange φ X b z') h := by
  apply injective_mk₀_constantRingMap_comp_mapExactFunctor φ X c
  dsimp only
  rw [mk₀_comp_mapExactFunctor_extRingChange, Ext.mapExactFunctor_comp,
    ← Ext.comp_assoc _ _ _ (zero_add a) h (by omega), mk₀_comp_mapExactFunctor_extRingChange,
    Ext.comp_assoc _ _ _ (add_zero a) (zero_add b) (by omega),
    mk₀_comp_mapExactFunctor_extRingChange, ← Ext.comp_assoc _ _ _ h (add_zero b) (by omega)]

end AlgebraicGeometry.Etale
