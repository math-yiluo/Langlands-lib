/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalSystems
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.LocallyConstantSections
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafCompose
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Sheaves of modules with finite locally constant underlying sheaves of sets

On a connected scheme `X` with a geometric point `s`, for an arbitrary ring `Λ` (e.g.
`ULift ℤ`, so for abelian sheaves with finite stalks):

- `AlgebraicGeometry.Scheme.FiniteLocallyConstant.isIso_of_bijective_sheafFiber_map`,
  `AlgebraicGeometry.Scheme.FiniteLocallyConstant.section_ext`: for finite locally constant
  sheaves of sets, the stalk at `s` detects isomorphisms, and global sections are determined by
  their germ at `s` (fibre functor of the Galois category of finite étale schemes);
- `AlgebraicGeometry.Scheme.IsSetFLC`: sheaves of `Λ`-modules whose underlying sheaf of sets is
  finite locally constant;
- `IsSetFLC.isIso_of_isIso_sheafFiber_map`, `IsSetFLC.sectionsGerm'_injective`,
  `IsSetFLC.isIso_constantSheafAdj_counit`: the corresponding statements for them, and constancy
  as soon as global sections map bijectively to the stalk at `s`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme


variable {Y : Scheme.{u}} [ConnectedSpace Y] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ Y)

/-- **The stalk at one geometric point detects isomorphisms of finite locally constant sheaves of
sets** on a connected scheme: through the Galois correspondence it is the fibre functor of the
Galois category of finite étale schemes, which reflects isomorphisms. -/
theorem FiniteLocallyConstant.isIso_of_bijective_sheafFiber_map {S S' : Y.FiniteLocallyConstant}
    (φ : S ⟶ S') (h : Function.Bijective ((pointSmallEtale s).sheafFiber.map φ.hom)) :
    IsIso φ := by
  set E := FiniteEtale.equivalenceFiniteLocallyConstant Y
  have hb : Function.Bijective ((FiniteEtale.fiber s).map (E.inverse.map φ)) := by
    have e : ∀ x, (FiniteEtale.fiber s).map (E.inverse.map φ) (stalkEquiv s S x).down =
        (stalkEquiv s S' ((pointSmallEtale s).sheafFiber.map φ.hom x)).down := fun x ↦
      (congrArg ULift.down (stalkEquiv_naturality s φ x)).symm
    have hc : ⇑((FiniteEtale.fiber s).map (E.inverse.map φ)) =
        (fun z ↦ (stalkEquiv s S' z).down) ∘ (pointSmallEtale s).sheafFiber.map φ.hom ∘
          (fun a ↦ (stalkEquiv s S).symm ⟨a⟩) := by
      funext a
      simp only [Function.comp_apply, ← e, Equiv.apply_symm_apply]
    rw [hc]
    exact (Equiv.ulift.bijective.comp (stalkEquiv s S').bijective).comp
      (h.comp ((stalkEquiv s S).symm.bijective.comp Equiv.ulift.symm.bijective))
  have : IsIso ((FiniteEtale.fiber s).map (E.inverse.map φ)) :=
    (ConcreteCategory.isIso_iff_bijective _).2 hb
  have : IsIso (E.inverse.map φ) := isIso_of_reflects_iso _ (FiniteEtale.fiber s)
  exact isIso_of_reflects_iso _ E.inverse

omit [ConnectedSpace Y] in
/-- A constant sheaf of sets with finite value is finite locally constant. -/
lemma isFiniteLocallyConstantSheafOfTypes_constantSheaf (F : Type (u + 1)) [Finite F] :
    IsFiniteLocallyConstantSheafOfTypes
      ((constantSheaf Y.smallEtaleTopology (Type (u + 1))).obj F) := by
  have : ((constantSheaf Y.smallEtaleTopology (Type (u + 1))).obj F).IsConstant
      Y.smallEtaleTopology := Sheaf.isConstant_of_iso _ (Iso.refl _)
  have : etalePrecoverage.{u}.HasIsos := inferInstanceAs (precoverage @Etale).HasIsos
  refine ⟨⟨.singleton (𝟙 Y) (Precoverage.mem_coverings_of_isIso _), fun _ ↦
    Sheaf.isConstant_over _ _⟩, ⟨fun Ω _ _ s ↦ ?_⟩⟩
  exact (ConcreteCategory.isFinitelyGenerated_iff_finite _).2
    (Finite.of_equiv _ ((pointSmallEtale s).sheafFiberConstantSheafIso F).symm.toEquiv)

/-- The terminal finite étale `Y`-scheme `Y`. -/
noncomputable abbrev FiniteEtale.terminal (Y : Scheme.{u}) : Y.FiniteEtale :=
  ⟨Etale.mk (𝟙 Y), inferInstanceAs (IsFinite (𝟙 Y))⟩

omit [ConnectedSpace Y] in
lemma FiniteEtale.subsingleton_fiber_terminal :
    Subsingleton ((FiniteEtale.fiber s).obj (FiniteEtale.terminal Y)) :=
  ⟨fun x x' ↦ fiber_ext s (((Category.comp_id _).symm.trans (fiber_left_comp s x)).trans
    ((fiber_left_comp s x').symm.trans (Category.comp_id _)))⟩

/-- **Global sections of a finite locally constant sheaf of sets on a connected scheme are
determined by their germ at one geometric point**: they are the morphisms from the terminal
sheaf, whose stalk is a point. -/
theorem FiniteLocallyConstant.section_ext (S : Y.FiniteLocallyConstant)
    {x x' : S.obj.obj.obj (op (Etale.mk (𝟙 Y)))}
    (h : (pointSmallEtale s).toPresheafFiber (Etale.mk (𝟙 Y)) (Over.homMk s) S.obj.obj x =
      (pointSmallEtale s).toPresheafFiber (Etale.mk (𝟙 Y)) (Over.homMk s) S.obj.obj x') :
    x = x' := by
  let One := (FiniteEtale.toFLC Y).obj (FiniteEtale.terminal Y)
  let ψ (z : S.obj.obj.obj (op (Etale.mk (𝟙 Y)))) : One ⟶ S :=
    ObjectProperty.homMk (Y.smallEtaleTopology.uliftYonedaEquiv.{u + 1}.symm z)
  have hsub : Subsingleton ((pointSmallEtale s).sheafFiber.obj One.obj) := by
    have := FiniteEtale.subsingleton_fiber_terminal s
    exact (((FiniteEtale.toFLCCompSheafFiberIso s).app
      (FiniteEtale.terminal Y)).toEquiv.trans Equiv.ulift).subsingleton
  have hgerm (z : S.obj.obj.obj (op (Etale.mk (𝟙 Y)))) (w) :
      (pointSmallEtale s).sheafFiber.map (ψ z).hom w =
        (pointSmallEtale s).toPresheafFiber (Etale.mk (𝟙 Y)) (Over.homMk s) S.obj.obj z := by
    rw [Subsingleton.elim w ((pointSmallEtale s).toPresheafFiber (Etale.mk (𝟙 Y))
      (Over.homMk s) One.obj.obj ⟨𝟙 _⟩)]
    have := ConcreteCategory.congr_hom ((pointSmallEtale s).toPresheafFiber_naturality
      (ψ z).hom.hom (Etale.mk (𝟙 Y)) (Over.homMk s))
      (show One.obj.obj.obj (op (Etale.mk (𝟙 Y))) from ⟨𝟙 _⟩)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
    refine this.trans (congrArg _ ?_)
    exact Y.smallEtaleTopology.uliftYonedaEquiv.{u + 1}.apply_symm_apply z
  have hψ : ψ x = ψ x' := FiniteLocallyConstant.hom_ext_of_sheafFiber s fun w ↦ by
    rw [hgerm, hgerm, h]
  have := congrArg (fun φ ↦ Y.smallEtaleTopology.uliftYonedaEquiv.{u + 1} φ.hom) hψ
  simpa [ψ] using this


variable {X : Scheme.{u}}

/-- Finite local constancy of sheaves of sets is invariant under isomorphism. -/
lemma IsFiniteLocallyConstantSheafOfTypes.of_iso
    {E E' : Sheaf X.smallEtaleTopology (Type (u + 1))}
    (e : E ≅ E') (h : IsFiniteLocallyConstantSheafOfTypes E) :
    IsFiniteLocallyConstantSheafOfTypes E' := by
  obtain ⟨⟨𝒰, h𝒰⟩, hfin⟩ := h
  refine ⟨⟨𝒰, fun i ↦ ?_⟩, ⟨fun Ω _ _ s ↦ ?_⟩⟩
  · obtain ⟨M, ⟨e0⟩⟩ := (h𝒰 i).mem_essImage
    exact Sheaf.isConstant_of_iso _
      (((X.smallEtaleTopology.overPullback _ _).mapIso e).symm ≪≫ e0.symm)
  · exact (hfin.isFinitelyGenerated_sheafFiber Ω s).of_iso ((pointSmallEtale s).sheafFiber.mapIso e)

variable {Λ : Type (u + 1)} [Ring Λ]

/-- A sheaf of `Λ`-modules whose underlying sheaf of sets is finite locally constant (e.g. a
locally constant sheaf of abelian groups with finite stalks), for an arbitrary ring `Λ`. -/
abbrev IsSetFLC (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) : Prop :=
  IsFiniteLocallyConstantSheafOfTypes
    ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj F)

/-- The underlying finite locally constant sheaf of sets. -/
abbrev IsSetFLC.toFLC {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (hF : IsSetFLC F) :
    X.FiniteLocallyConstant :=
  ⟨_, hF⟩

/-- Forgetting the module structure reflects isomorphisms of sheaves. -/
lemma isIso_of_isIso_sheafCompose_forget_map
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (φ : F ⟶ G)
    [h : IsIso ((sheafCompose X.smallEtaleTopology
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).map φ)] : IsIso φ := by
  have : ∀ U, IsIso (φ.hom.app U) := fun U ↦ by
    have : IsIso ((sheafToPresheaf _ _).map ((sheafCompose X.smallEtaleTopology
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).map φ)) := inferInstance
    have : IsIso ((CategoryTheory.forget (ModuleCat.{u + 1} Λ)).map (φ.hom.app U)) :=
      inferInstanceAs (IsIso (((sheafToPresheaf _ _).map ((sheafCompose X.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).map φ)).app U))
    exact isIso_of_reflects_iso _ (CategoryTheory.forget (ModuleCat.{u + 1} Λ))
  have : IsIso ((sheafToPresheaf _ _).map φ) := NatIso.isIso_of_isIso_app φ.hom
  exact isIso_of_reflects_iso φ (sheafToPresheaf _ _)

section Connected

variable [ConnectedSpace X] {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)

/-- **The stalk at one geometric point detects isomorphisms between sheaves of modules whose
underlying sheaves of sets are finite locally constant** on a connected scheme (any ring `Λ`). -/
theorem IsSetFLC.isIso_of_isIso_sheafFiber_map
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (hF : IsSetFLC F) (hG : IsSetFLC G) (φ : F ⟶ G)
    [IsIso ((pointSmallEtale s).sheafFiber.map φ)] : IsIso φ := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let e := (pointSmallEtale s).sheafFiberCompIso (CategoryTheory.forget (ModuleCat.{u + 1} Λ))
  let φ' : hF.toFLC ⟶ hG.toFLC := ObjectProperty.homMk
    ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).map φ)
  have hb : Function.Bijective ((pointSmallEtale s).sheafFiber.map φ'.hom) := by
    have h := e.hom.naturality φ
    rw [← Iso.app_hom, ← Iso.eq_comp_inv] at h
    rw [← ConcreteCategory.isIso_iff_bijective]
    change IsIso ((sheafCompose _ _ ⋙ (pointSmallEtale s).sheafFiber).map φ)
    rw [h]
    have : IsIso (((pointSmallEtale s).sheafFiber ⋙
        CategoryTheory.forget (ModuleCat.{u + 1} Λ)).map φ) :=
      inferInstanceAs (IsIso ((CategoryTheory.forget _).map ((pointSmallEtale s).sheafFiber.map φ)))
    infer_instance
  have : IsIso φ' := FiniteLocallyConstant.isIso_of_bijective_sheafFiber_map s φ' hb
  have : IsIso ((sheafCompose X.smallEtaleTopology
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).map φ) :=
    inferInstanceAs (IsIso ((ObjectProperty.ι _).map φ'))
  exact isIso_of_isIso_sheafCompose_forget_map φ

/-- The germ at `s` of global sections. -/
noncomputable abbrev sectionsGerm' (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    G.obj.obj (op (Etale.mk (𝟙 X))) ⟶ (pointSmallEtale s).sheafFiber.obj G :=
  (pointSmallEtale s).toPresheafFiber (Etale.mk (𝟙 X)) (Over.homMk s) G.obj

/-- **Global sections are determined by their germ at one geometric point**, for sheaves of
modules whose underlying sheaves of sets are finite locally constant on a connected scheme. -/
theorem IsSetFLC.sectionsGerm'_injective {G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (hG : IsSetFLC G) : Function.Injective (sectionsGerm' s G) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  intro x x' h
  apply FiniteLocallyConstant.section_ext s hG.toFLC
  have hc := (pointSmallEtale s).toPresheafFiber_presheafFiberCompIso_hom_app (Etale.mk (𝟙 X))
    (Over.homMk s) G.obj (F := CategoryTheory.forget (ModuleCat.{u + 1} Λ))
  have h1 := ConcreteCategory.congr_hom hc x
  have h2 := ConcreteCategory.congr_hom hc x'
  rw [ConcreteCategory.comp_apply] at h1 h2
  apply (ConcreteCategory.bijective_of_isIso
    (((pointSmallEtale s).presheafFiberCompIso
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).hom.app G.obj)).1
  refine h1.trans (Eq.trans ?_ h2.symm)
  exact h

omit [ConnectedSpace X] in
/-- The constant sheaf of modules with finite value has finite locally constant underlying sheaf
of sets. -/
lemma isSetFLC_constantSheaf (M : ModuleCat.{u + 1} Λ) [Finite M] :
    IsSetFLC ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) := by
  have : X.smallEtaleTopology.PreservesSheafification
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    GrothendieckTopology.instPreservesSheafification _ _
  exact IsFiniteLocallyConstantSheafOfTypes.of_iso
    ((constantSheafCompSheafComposeIso X.smallEtaleTopology
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).app M).symm
    (isFiniteLocallyConstantSheafOfTypes_constantSheaf (Y := X) (M : Type (u + 1)))

/-- **A sheaf of modules with finite locally constant underlying sheaf of sets on a connected
scheme is constant as soon as its global sections map bijectively to one stalk.** -/
theorem IsSetFLC.isIso_constantSheafAdj_counit
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (hG : IsSetFLC G)
    (h : Function.Bijective (sectionsGerm' s G)) :
    IsIso ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
      (Etale.isTerminalMkId X)).counit.app G) := by
  let adj := constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ) (Etale.isTerminalMkId X)
  let M := (sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
    (op (Etale.mk (𝟙 X))) |>.obj G
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have hstalk := (pointSmallEtale s).sheafFiberConstantSheafIso_inv_comp_sheafFiber_map
    (Etale.isTerminalMkId X) (Over.homMk s) M G (adj.counit.app G)
  have h1 : adj.homEquiv M G (adj.counit.app G) = 𝟙 _ := by
    rw [Adjunction.homEquiv_unit]
    exact adj.right_triangle_components G
  rw [h1, Category.id_comp, Iso.inv_comp_eq] at hstalk
  have : IsIso ((pointSmallEtale s).sheafFiber.map (adj.counit.app G)) := by
    rw [hstalk]
    have : IsIso (sectionsGerm' s G) := (ConcreteCategory.isIso_iff_bijective _).2 h
    infer_instance
  have hfin : Finite M := by
    have : Finite ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.obj G) := by
      have h0 : Finite ((pointSmallEtale s).sheafFiber.obj ((sheafCompose X.smallEtaleTopology
          (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj G)) :=
        (ConcreteCategory.isFinitelyGenerated_iff_finite _).1
          (hG.2.isFinitelyGenerated_sheafFiber Ω s)
      exact (((pointSmallEtale s).sheafFiberCompIso
        (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).app G).toEquiv.finite_iff.mp h0
    exact Finite.of_injective _ h.1
  exact IsSetFLC.isIso_of_isIso_sheafFiber_map s (isSetFLC_constantSheaf M) hG _

end Connected

end AlgebraicGeometry.Scheme
