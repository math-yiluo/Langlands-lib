/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Evaluation.TerminalScalarRealization

/-! The terminal sections adjunction of the terminal scalar realization.

Source: Hemo--Richarz--Scholbach, Lemma 4.1(1), equations (3.1)--(3.2), Remark 3.2.
(blueprint: new-lem-zl-contractible-realization-sections-adjunction-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.CondensedRing.Evaluation

private def constantPresheafHomEquiv
    {C : Type (u + 1)} [Category.{u} C] (R : Type (u + 1)) [CommRing R]
    (U : C) (hU : IsTerminal U) (M : ModuleCat.{u + 1} R)
    (N : PresheafOfModules.{u + 1} ((Functor.const Cᵒᵖ).obj (RingCat.of R))) :
    ((siteConstantModulePresheafGeneral (C := C) R).obj M ⟶ N) ≃
      (M ⟶ N.obj (Opposite.op U)) where
  toFun f := f.app (Opposite.op U)
  invFun g :=
    { app := fun V ↦ g ≫ N.map (hU.from V.unop).op
      naturality := by
        intro V W f
        ext x
        change N.map (hU.from W.unop).op (g x) =
          N.map f (N.map (hU.from V.unop).op (g x))
        rw [← N.map_comp_apply]
        have h : (hU.from W.unop).op = (hU.from V.unop).op ≫ f := by
          apply Quiver.Hom.unop_inj
          exact hU.hom_ext _ _
        rw [h] }
  left_inv f := by
    ext V x
    exact (PresheafOfModules.naturality_apply f (hU.from V.unop).op x).symm
  right_inv g := by
    ext x
    change N.map (hU.from U).op (g x) = g x
    have h : hU.from U = 𝟙 U := hU.hom_ext _ _
    rw [h]
    change N.map (𝟙 (Opposite.op U)) (g x) = g x
    rw [N.map_id]
    rfl

private def constantPresheafAdjunction
    {C : Type (u + 1)} [Category.{u} C] (R : Type (u + 1)) [CommRing R]
    (U : C) (hU : IsTerminal U) :
    siteConstantModulePresheafGeneral (C := C) R ⊣
      PresheafOfModules.evaluation ((Functor.const Cᵒᵖ).obj (RingCat.of R)) (Opposite.op U) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := constantPresheafHomEquiv R U hU
      homEquiv_naturality_left_symm := by intros; ext V x; rfl
      homEquiv_naturality_right := by intros; rfl }

section ScalarExtension
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C}
open SheafOfModules
open scoped ChangeOfRings

private abbrev coefficientRing (S : Sheaf J CommRingCat.{u + 1}) :=
  (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S

private abbrev extensionRestriction
    {R : Type (u + 1)} [CommRing R] {S : Sheaf J CommRingCat.{u + 1}}
    (c : realizationRing J R ⟶ S) :=
  SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c)

private abbrev extensionPresheaf
    {R : Type (u + 1)} [CommRing R] {S : Sheaf J CommRingCat.{u + 1}}
    (c : realizationRing J R ⟶ S) (M : realizationModules J R) :
    PresheafOfModules.{u + 1} (coefficientRing S).obj :=
  SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
    (C := C) (J := J) c M

private theorem extensionPresheaf_one
    {R : Type (u + 1)} [CommRing R] {S : Sheaf J CommRingCat.{u + 1}}
    (c : realizationRing J R ⟶ S) (M : realizationModules J R)
    {X Y : Cᵒᵖ} (i : X ⟶ Y) (m : M.val.obj X) :
    (extensionPresheaf c M).map i
        ((1 : S.obj.obj X) ⊗ₜ[(realizationRing J R).obj.obj X, (c.hom.app X).hom] m) =
      (1 : S.obj.obj Y) ⊗ₜ[(realizationRing J R).obj.obj Y, (c.hom.app Y).hom]
        PresheafOfModulesOfCommRing.map (R := (realizationRing J R).obj) M.val i m := by
  have h := SheafOfModules.changeOfRingsMap_tmulOfUniverses.{u, u + 1, u + 1, u + 1}
    c M i (1 : S.obj.obj X) m
  rw [map_one] at h
  exact h

private noncomputable def tensorPresheafFunctor
    {R : Type (u + 1)} [CommRing R] {S : Sheaf J CommRingCat.{u + 1}}
    (c : realizationRing J R ⟶ S) :
    realizationModules J R ⥤ PresheafOfModules.{u + 1} (coefficientRing S).obj where
  obj M := extensionPresheaf c M
  map {M N} f :=
    show extensionPresheaf c M ⟶
      extensionPresheaf c N from
    { app := fun W ↦
        (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (c.hom.app W).hom).map (f.val.app W)
      naturality := SheafOfModules.changeOfRingsHom_naturalityOfUniverses.{u, u + 1, u + 1, u + 1}
        c _ f }
  map_id M := by
    ext W : 1
    change (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (c.hom.app W).hom).map (𝟙 _) = _
    exact (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (c.hom.app W).hom).map_id _
  map_comp f g := by
    ext W : 1
    exact (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (c.hom.app W).hom).map_comp _ _

private noncomputable def tensorFunctor
    {R : Type (u + 1)} [CommRing R] {S : Sheaf J CommRingCat.{u + 1}}
    (c : realizationRing J R ⟶ S) :
    realizationModules J R ⥤ SheafOfModules.{u + 1} (coefficientRing S) :=
  SheafOfModules.flatScalarExtension J c

private noncomputable def tensorToRestriction
    {R : Type (u + 1)} [CommRing R] {S : Sheaf J CommRingCat.{u + 1}}
    (c : realizationRing J R ⟶ S)
    (M : realizationModules J R) (H : SheafOfModules.{u + 1} (coefficientRing S))
    (f : extensionPresheaf c M ⟶ H.val) :
    M ⟶ (extensionRestriction c).obj H where
  val :=
    { app := fun W ↦
        ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars.{u + 1, u + 1, u + 1}
          (c.hom.app W).hom (f.app W)
      naturality := by
        intro X Y i
        ext m
        change f.app Y ((1 : S.obj.obj Y) ⊗ₜ[(realizationRing J R).obj.obj Y, (c.hom.app Y).hom]
          PresheafOfModulesOfCommRing.map (R := (realizationRing J R).obj) M.val i m) =
            H.val.map i (f.app X
              ((1 : S.obj.obj X) ⊗ₜ[(realizationRing J R).obj.obj X, (c.hom.app X).hom] m))
        have h := PresheafOfModules.naturality_apply f i
          ((1 : S.obj.obj X) ⊗ₜ[(realizationRing J R).obj.obj X, (c.hom.app X).hom] m)
        rw [extensionPresheaf_one c M i m] at h
        exact h }

private noncomputable def restrictionToTensor
    {R : Type (u + 1)} [CommRing R] {S : Sheaf J CommRingCat.{u + 1}}
    (c : realizationRing J R ⟶ S)
    (M : realizationModules J R) (H : SheafOfModules.{u + 1} (coefficientRing S))
    (g : M ⟶ (extensionRestriction c).obj H) :
    extensionPresheaf c M ⟶ H.val where
  app W :=
    ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u + 1}
      (c.hom.app W).hom (g.val.app W)
  naturality := by
    intro X Y i
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    have h := PresheafOfModules.naturality_apply g.val i m
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u + 1}
      (c.hom.app Y).hom (g.val.app Y)
        ((extensionPresheaf c M).map i
          ((1 : S.obj.obj X) ⊗ₜ[(realizationRing J R).obj.obj X, (c.hom.app X).hom] m)) =
      H.val.map i
        (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u + 1}
          (c.hom.app X).hom (g.val.app X)
          ((1 : S.obj.obj X) ⊗ₜ[(realizationRing J R).obj.obj X, (c.hom.app X).hom] m))
    rw [extensionPresheaf_one c M i m]
    have atOne (W : Cᵒᵖ) (n : M.val.obj W) :
        ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u + 1}
          (c.hom.app W).hom (g.val.app W)
            ((1 : S.obj.obj W) ⊗ₜ[(realizationRing J R).obj.obj W, (c.hom.app W).hom] n) =
              g.val.app W n := by
      exact congrArg (fun f : M.val.obj W ⟶
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (c.hom.app W).hom).obj (H.val.obj W) ↦ f n)
        ((ModuleCat.ExtendRestrictScalarsAdj.homEquiv.{u + 1, u + 1, u + 1}
          (c.hom.app W).hom).apply_symm_apply (g.val.app W))
    rw [atOne, atOne]
    exact h

private noncomputable def tensorPresheafHomEquiv
    {R : Type (u + 1)} [CommRing R] {S : Sheaf J CommRingCat.{u + 1}}
    (c : realizationRing J R ⟶ S)
    (M : realizationModules J R) (H : SheafOfModules.{u + 1} (coefficientRing S)) :
    (extensionPresheaf c M ⟶ H.val) ≃
      (M ⟶ (extensionRestriction c).obj H) where
  toFun := tensorToRestriction c M H
  invFun := restrictionToTensor c M H
  left_inv f := by
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv.{u + 1, u + 1, u + 1}
      (c.hom.app W).hom).symm_apply_apply (f.app W)
  right_inv g := by
    apply SheafOfModules.hom_ext
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv.{u + 1, u + 1, u + 1}
      (c.hom.app W).hom).apply_symm_apply (g.val.app W)

private noncomputable def tensorHomEquiv
    {R : Type (u + 1)} [CommRing R] {S : Sheaf J CommRingCat.{u + 1}}
    (c : realizationRing J R ⟶ S)
    (M : realizationModules J R) (H : SheafOfModules.{u + 1} (coefficientRing S)) :
    ((tensorFunctor c).obj M ⟶ H) ≃ (M ⟶ (extensionRestriction c).obj H) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (coefficientRing S).obj)).homEquiv _ _).trans
    (tensorPresheafHomEquiv c M H)

private theorem tensorHomEquiv_naturality_left
    {R : Type (u + 1)} [CommRing R] {S : Sheaf J CommRingCat.{u + 1}}
    (c : realizationRing J R ⟶ S)
    {M N : realizationModules J R} (a : M ⟶ N)
    (H : SheafOfModules.{u + 1} (coefficientRing S)) (f : (tensorFunctor c).obj N ⟶ H) :
    tensorHomEquiv c M H ((tensorFunctor c).map a ≫ f) =
      a ≫ tensorHomEquiv c N H f := by
  change tensorPresheafHomEquiv c M H
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (coefficientRing S).obj)).homEquiv _ _
        ((PresheafOfModules.sheafification (𝟙 (coefficientRing S).obj)).map
          ((tensorPresheafFunctor c).map a) ≫ f)) = _
  rw [Adjunction.homEquiv_naturality_left]
  ext W m
  change ((PresheafOfModules.sheafificationAdjunction (𝟙 (coefficientRing S).obj)).homEquiv
    (extensionPresheaf c N) H f).app W
      ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (c.hom.app W).hom).map (a.val.app W)
        ((1 : S.obj.obj W) ⊗ₜ[(realizationRing J R).obj.obj W, (c.hom.app W).hom] m)) = _
  rw [ModuleCat.ExtendScalars.map_tmul]
  rfl

private theorem tensorHomEquiv_naturality_right
    {R : Type (u + 1)} [CommRing R] {S : Sheaf J CommRingCat.{u + 1}}
    (c : realizationRing J R ⟶ S)
    (M : realizationModules J R)
    {H H' : SheafOfModules.{u + 1} (coefficientRing S)}
    (f : (tensorFunctor c).obj M ⟶ H) (b : H ⟶ H') :
    tensorHomEquiv c M H' (f ≫ b) =
      tensorHomEquiv c M H f ≫ (extensionRestriction c).map b := by
  change tensorPresheafHomEquiv c M H'
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (coefficientRing S).obj)).homEquiv _ _
        (f ≫ b)) = _
  rw [Adjunction.homEquiv_naturality_right]
  rfl

private noncomputable def tensorAdjunction
    {R : Type (u + 1)} [CommRing R] {S : Sheaf J CommRingCat.{u + 1}}
    (c : realizationRing J R ⟶ S) : tensorFunctor c ⊣ extensionRestriction c :=
  Adjunction.mkOfHomEquiv
    { homEquiv := tensorHomEquiv c
      homEquiv_naturality_left_symm := by
        intro M N H a g
        apply (tensorHomEquiv c M H).injective
        rw [Equiv.apply_symm_apply, tensorHomEquiv_naturality_left,
          Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun f b ↦ tensorHomEquiv_naturality_right c _ f b }

end ScalarExtension

/-- The terminal scalar realization is left adjoint to the terminal sections functor.

Source: Hemo--Richarz--Scholbach, Lemma 4.1(1), equations (3.1)--(3.2), Remark 3.2.
(blueprint: new-lem-zl-contractible-realization-sections-adjunction-data).

Proof: write `A = O_sec(U)`, `A_J` for its constant ring sheaf, `c_J` for the constant
module realization, `s : A_J → O_sec` for `scalarMap` and `E` for the internal/section
module equivalence. For an `O`-module `N`, `E` preserves sections, so
`Hom_O(L M, N) = Hom_{O_sec}(E L M, E N)`. By the ringed-topoi module adjunction along
`s` this is `Hom_{A_J}(c_J M, Res_s E N)`, and by the universal property of module
sheafification it is the set of restriction-compatible families of `A`-linear maps
`M → E N(V)`. Since `U` is terminal, such a family is determined by its component
`M → E N(U) = sections N`, and every `A`-linear map `g` gives one by restriction along
the unique `V → U`; the `A`-structure on `E N(U)` through `s_U` is the given one by the
triangle identity. The bijection evaluates at `U` on `1 ⊗ m`, with inverse
`o ⊗ m ↦ o · g(m)|_V`; naturality and both inverse identities hold on pure tensors. -/
theorem contractible_realization_sections_adjunction_data
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) [(J.W (A := Ab.{u + 1})).IsMonoidal]
    (O : Sheaf J Ab.{u + 1}) [MonObj O] [IsCommMonObj O]
    (U : C) (hU : IsTerminal U) :
    Nonempty (terminalScalarRealization J O U hU ⊣ sections J O U) := by
  let R := A J O U
  let S := ringSheaf J O
  let c := scalarMap J O U hU
  let η := realizationRingUnit J R
  let e := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J O
  let ev : PresheafOfModules.{u + 1} ((Functor.const Cᵒᵖ).obj (RingCat.of R)) ⥤
      ModuleCat.{u + 1} R :=
    PresheafOfModules.evaluation _ (Opposite.op U)
  let q := SheafOfModules.forget.{u + 1}
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (realizationRing J R)) ⋙
      PresheafOfModules.restrictScalars.{u + 1} η
  have hscalar (r : R) : c.hom.app (Opposite.op U) (η.app (Opposite.op U) r) = r := by
    have h := ConcreteCategory.congr_hom
      ((constantSheafAdj J CommRingCat.{u + 1} hU).right_triangle_components
        (Y := S)) r
    exact h
  let := (realizationRingUnit_locallyBijective J R).1
  let := (realizationRingUnit_locallyBijective J R).2
  let a := (((constantPresheafAdjunction R U hU).comp
    (PresheafOfModules.sheafificationAdjunction η)).comp
      (tensorAdjunction c)).comp e.symm.toAdjunction
  let G := e.functor ⋙ (extensionRestriction c ⋙ (q ⋙ ev))
  let H := sections J O U
  let β : G ≅ H :=
    NatIso.ofComponents (fun N ↦
      { hom := ModuleCat.ofHom (X := G.obj N) (Y := H.obj N)
          { toFun := fun x ↦ x
            map_add' := fun _ _ ↦ rfl
            map_smul' := by
              intro r x
              change (c.hom.app (Opposite.op U) (η.app (Opposite.op U) r)) •
                (show (e.functor.obj N).val.obj (Opposite.op U) from x) =
                  r • (show (e.functor.obj N).val.obj (Opposite.op U) from x)
              rw [hscalar] }
        inv := ModuleCat.ofHom (X := H.obj N) (Y := G.obj N)
          { toFun := fun x ↦ x
            map_add' := fun _ _ ↦ rfl
            map_smul' := by
              intro r x
              change r • (show (e.functor.obj N).val.obj (Opposite.op U) from x) =
                (c.hom.app (Opposite.op U) (η.app (Opposite.op U) r)) •
                  (show (e.functor.obj N).val.obj (Opposite.op U) from x)
              rw [hscalar] }
        hom_inv_id := by ext x; rfl
        inv_hom_id := by ext x; rfl })
      (by intro N N' f; ext x; rfl)
  exact ⟨a.ofNatIsoRight β⟩

end AlgebraicGeometry.ProEtale.CondensedRing.Evaluation
