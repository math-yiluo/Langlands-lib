/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Detection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Complement

import WeilConjectures.AlgebraicGeometry.ProEtale.ClosedSiteAdjunction
import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative

/-!
# The pushforward along a closed immersion on pro-étale sheaves of modules

This is the pro-étale counterpart of
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.ClosedImmersion`.

Let `i : Z ⟶ X` be a closed immersion and `j : U ⟶ X` a quasi-compact open immersion onto
the complement of its range. For pro-étale sheaves of modules over a ring `R`:

* the restrictions `i^*` and `j^*` jointly detect zero objects
  (`AlgebraicGeometry.ProEtale.isZero_of_isZero_upperStar_of_isCompl`, blueprint
  `proposition-extension-zero-restriction-closed-subscheme`), hence jointly detect isomorphisms;
* `i_*` is exact (`AlgebraicGeometry.ProEtale.preservesFiniteColimits_lowerStar_of_isCompl`,
  blueprint `proposition-extension-zero-restriction-closed-subscheme--4`);
* a sheaf lies in the essential image of `i_*` if and only if its restriction to `U` vanishes,
  and then the unit `F ⟶ i_* i^* F` is an isomorphism
  (`AlgebraicGeometry.ProEtale.lowerStar_essImage_iff_of_isCompl`,
  `AlgebraicGeometry.ProEtale.isIso_upperStarLowerStarAdjunction_unit_app_of_isCompl`,
  blueprint `lemma-passing-schematic-closure--1`).

All three rest on the full faithfulness of `i_*`, that the counit `i^* i_* G ⟶ G` is an
isomorphism (`AlgebraicGeometry.ProEtale.isIso_upperStarLowerStarAdjunction_counit`, proved for
sheaves with values in any Grothendieck abelian category, blueprint
`proposition-extension-zero-restriction-closed-subscheme--5` of the subsection
`proposition-extension-zero-restriction-closed-subscheme`).

## Implementation notes

The detection statement is the case of the finite jointly surjective family `{i, j}` of the
general `AlgebraicGeometry.ProEtale.eq_zero_of_forall_upperStar_map_eq_zero`: a section whose
restrictions along `i` and `j` vanish vanishes on weakly étale neighbourhoods of the points of
`Z` and `U`, and these form a pro-étale cover because both `i` and `j` are quasi-compact. This
replaces the blueprint's lifting of coverings of the closed fibre.

Exactness of `i_*` then follows from the counit isomorphism: the cokernel of `i_* φ` for an
epimorphism `φ` has vanishing restriction to `Z`, since `i^* i_* φ ≅ φ`, and to `U`, since
`j^* i_* = 0`.
-/

@[expose] public section

universe u u'

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable {Z U X : Scheme.{u}}

private lemma isIso_map_counit_of_local_adjunction
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {F₁ : A ⥤ C} {U₁ : C ⥤ A} {F₂ : B ⥤ D} {U₂ : D ⥤ B}
    (ai : L₁ ⊣ R₁) (ai' : L₂ ⊣ R₂) (aj : F₁ ⊣ U₁) (aj' : F₂ ⊣ U₂)
    (α : TwoSquare U₂ R₂ R₁ U₁) [IsIso α]
    (hb : IsIso (((mateEquiv aj' aj).symm α)))
    (hc : IsIso ai'.counit) (M : B) : IsIso (F₂.map (ai.counit.app M)) := by
  let β := (mateEquiv aj' aj).symm α
  let γ := (mateEquiv ai ai').symm β
  have : IsIso β := hb
  have : IsIso γ := by
    dsimp [γ, β]
    rw [iterated_mateEquiv_conjugateEquiv_symm ai ai' aj aj']
    infer_instance
  have h := mateEquiv_counit_symm ai ai' β M
  have : IsIso ai'.counit := hc
  have : IsIso (L₂.map (β.app M) ≫ ai'.counit.app (F₂.obj M)) := inferInstance
  rw [h] at this
  exact IsIso.of_isIso_comp_left (γ.app _) _

section

variable (C : Type u') [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]

omit [Abelian C] [IsGrothendieckAbelian.{u + 1} C] in
private lemma closedSitePrecompFullyFaithful (A : Type u) [CommRing A] (I : Ideal A) :
    Nonempty (((Functor.whiskeringLeft _ _ C).obj
      (AffineProEt.closedSiteBaseChange A I).op).FullyFaithful) := by
  obtain ⟨adj, h⟩ := AffineProEt.exists_closedSiteAdjunction A I
  have : IsIso adj.unit := h
  let adjp := adj.op.whiskerLeft C
  have : ∀ F, IsIso (adjp.counit.app F) := fun F => by
    have : ∀ X, IsIso ((adjp.counit.app F).app X) := fun X => by
      dsimp [adjp, Adjunction.whiskerLeft]
      simp only [Category.id_comp, Category.comp_id]
      change IsIso (F.map (adj.unit.app X.unop).op)
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  have : IsIso adjp.counit := NatIso.isIso_of_isIso_app _
  exact ⟨adjp.fullyFaithfulROfIsIsoCounit⟩

private lemma isIso_closedCounit_of_quotient (A : Type u) [CommRing A] (I : Ideal A) :
    IsIso (upperStarLowerStarAdjunction C
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).counit := by
  obtain ⟨hpre⟩ := closedSitePrecompFullyFaithful C A I
  let F := lowerStar C
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
  let RX := (AffineProEt.toProEt (Spec (.of A))).sheafPushforwardContinuous
    C (AffineProEt.topology (Spec (.of A))) (ProEt.topology (Spec (.of A))) ⋙
    sheafToPresheaf (AffineProEt.topology (Spec (.of A))) C
  let RZ := (AffineProEt.toProEt (Spec (.of (A ⧸ I)))).sheafPushforwardContinuous
    C (AffineProEt.topology (Spec (.of (A ⧸ I))))
      (ProEt.topology (Spec (.of (A ⧸ I)))) ⋙
    sheafToPresheaf (AffineProEt.topology (Spec (.of (A ⧸ I)))) C
  have hRZ : RZ.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful _
  have hcomp : (F ⋙ RX).FullyFaithful := hRZ.comp hpre
  have hF : F.FullyFaithful := hcomp.ofCompFaithful
  have : F.Full := hF.full
  have : F.Faithful := hF.faithful
  exact Adjunction.counit_isIso_of_R_fully_faithful _

private lemma isIso_closedCounit_of_isAffine {Z X : Scheme.{u}} [IsAffine X]
    (i : Z ⟶ X) [IsClosedImmersion i] :
    IsIso (upperStarLowerStarAdjunction C i).counit := by
  obtain ⟨I, e, he⟩ := (IsClosedImmersion.Spec_iff (f := i ≫ X.isoSpec.hom)).mp inferInstance
  have hq := isIso_closedCounit_of_quotient C (Γ(X, ⊤)) I
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have : (q)_*[C].Full :=
    (upperStarLowerStarAdjunction C q).fullyFaithfulROfIsIsoCounit.full
  have : (q)_*[C].Faithful :=
    (upperStarLowerStarAdjunction C q).fullyFaithfulROfIsIsoCounit.faithful
  have h : ((e.hom)_*[C] ⋙ (q)_*[C]).FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful _
  have h' := h.ofIso (lowerStarComp C e.hom q ≪≫
    lowerStarCongr C he.symm)
  have h'' : ((i)_*[C] ⋙
      (X.isoSpec.hom)_*[C]).FullyFaithful :=
    h'.ofIso (lowerStarComp C i X.isoSpec.hom).symm
  have hF := h''.ofCompFaithful
  have := hF.full
  have := hF.faithful
  exact Adjunction.counit_isIso_of_R_fully_faithful _

private lemma isIso_closedCounit_localization {U' U Z' Z : Scheme.{u}}
    {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}
    [WeaklyEtale j] [WeaklyEtale j'] (sq : IsPullback g' j' j g'')
    (hc : IsIso (upperStarLowerStarAdjunction C g').counit)
    (F : Sheaf (ProEt.topology Z') C) :
    IsIso ((localizationRestriction C j' inferInstance).map
      ((upperStarLowerStarAdjunction C g'').counit.app F)) := by
  let ai := upperStarLowerStarAdjunction C g''
  let ai' := upperStarLowerStarAdjunction C g'
  let aj := localizationRestrictionLowerStarAdjunction C j inferInstance
  let aj' := localizationRestrictionLowerStarAdjunction C j' inferInstance
  let α := TwoSquare.mk _ _ _ _ (squareLowerStarIso C sq.toCommSq).hom
  let β := (mateEquiv aj' aj).symm α
  have hβ : β = localizationRestrictionBaseChangeMap
      C sq.toCommSq := by
    apply (mateEquiv aj' aj).injective
    change (mateEquiv aj' aj) ((mateEquiv aj' aj).symm α) = _
    rw [Equiv.apply_symm_apply]
    exact (mateEquiv_localizationRestrictionBaseChangeMap
      C sq.toCommSq).symm
  have : IsIso β := by
    rw [hβ]
    exact isIso_localizationRestrictionBaseChangeMap_of_isPullback _ sq
  exact isIso_map_counit_of_local_adjunction ai ai' aj aj' α this hc F


/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme--5` (subsection
`proposition-extension-zero-restriction-closed-subscheme`): for a closed immersion `i : Z ⟶ X` the
counit `i^* i_* G ⟶ G` of the pro-étale adjunction `i^* ⊣ i_*` is an isomorphism on all pro-étale
sheaves with values in a Grothendieck abelian category `C` (for instance modules over a ring
or abelian groups); so `i_*` is fully faithful, without a constructibility hypothesis.

Proof: on the affine pro-étale bases of Spec A and Spec (A/I), closed base change is
right adjoint to the closed-site lift with invertible unit. Opposites and precomposition
therefore make direct image fully faithful on presheaves. Restriction to these bases is
an equivalence on sheaves, so the same holds for sheaves. An arbitrary closed
immersion into an affine scheme is isomorphic to such a quotient immersion. Finally,
restrict the counit to the inverse image of an affine open cover of the target. Weakly
étale base change and the double-mate identity identify these restrictions with the affine
counits, up to isomorphisms. Open-cover conservativity proves the global claim. -/
theorem isIso_upperStarLowerStarAdjunction_counit (i : Z ⟶ X) [IsClosedImmersion i] :
    IsIso (upperStarLowerStarAdjunction C i).counit := by
  have happ (F : Sheaf (ProEt.topology Z) C) :
      IsIso ((upperStarLowerStarAdjunction C i).counit.app F) := by
    let U (k : X.affineCover.I₀) := pullback (X.affineCover.f k) i
    let j (k : X.affineCover.I₀) : U k ⟶ Z := pullback.snd _ _
    have : ∀ k, IsOpenImmersion (j k) := fun k => inferInstance
    have hsurj : ∀ z, ∃ k, z ∈ Set.range (j k).base := by
      intro z
      obtain ⟨x, hx⟩ := X.affineCover.covers (i.base z)
      obtain ⟨w, -, hw⟩ := Scheme.Pullback.exists_preimage_pullback x z hx
      exact ⟨X.affineCover.idx (i.base z), w, hw⟩
    have hcover : Presieve.ofArrows U j ∈ Scheme.proetalePrecoverage Z :=
      Scheme.zariskiPrecoverage_le_proetalePrecoverage _
        ((Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨hsurj, fun k => this k⟩)
    refine isIso_of_isIso_localizationRestriction C _ j hcover
      fun k => ?_
    exact isIso_closedCounit_localization C (IsPullback.of_hasPullback (X.affineCover.f k) i)
      (isIso_closedCounit_of_isAffine C (pullback.fst (X.affineCover.f k) i)) F
  exact NatIso.isIso_of_isIso_app _

attribute [instance] isIso_upperStarLowerStarAdjunction_counit

end

variable (R : Type (u + 1)) [Ring R]

/-- The pushforward along a closed immersion is fully faithful on pro-étale sheaves of
modules. -/
noncomputable def fullyFaithfulLowerStar (i : Z ⟶ X) [IsClosedImmersion i] :
    ((i)_*[ModuleCat.{u + 1} R]).FullyFaithful :=
  (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).fullyFaithfulROfIsIsoCounit

instance full_lowerStar (i : Z ⟶ X) [IsClosedImmersion i] :
    ((i)_*[ModuleCat.{u + 1} R]).Full :=
  (fullyFaithfulLowerStar R i).full

instance faithful_lowerStar (i : Z ⟶ X) [IsClosedImmersion i] :
    ((i)_*[ModuleCat.{u + 1} R]).Faithful :=
  (fullyFaithfulLowerStar R i).faithful

section Disjoint

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The restriction of `i_* G` to an open `j : U ⟶ X` missing the range of `i` vanishes: its
sections over `T` are the sections of `G` over the empty scheme `T ×_X Z`. Here `i` is
arbitrary. -/
lemma isZero_upperStar_lowerStar_of_disjoint (i : Z ⟶ X) (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Disjoint (Set.range i.base) (Set.range j.base)) (G : Sheaf (ProEt.topology Z) A) :
    IsZero ((j)^*[A].obj ((i)_*[A].obj G)) :=
  (isZero_openImmersionRestriction_lowerStar A i j (Set.disjoint_iff_inter_eq_empty.1 hij)
    G).of_iso ((upperStarIsoOpenImmersionRestriction A j).app _)

end Disjoint

variable {R}

variable (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]

omit [IsOpenImmersion j] in
/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme`: let `i : Z ⟶ X` be a closed
immersion with quasi-compact open complement `j : U ⟶ X`. A pro-étale sheaf of modules `F` on `X`
with `i^* F = 0` and `j^* F = 0` is zero.

This is `AlgebraicGeometry.ProEtale.eq_zero_of_forall_upperStar_map_eq_zero` for the identity
of `F` and the quasi-compact jointly surjective family `{i, j}`. -/
theorem isZero_of_isZero_upperStar_of_isCompl
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R))
    (hi : IsZero ((i)^*[ModuleCat.{u + 1} R].obj F))
    (hj : IsZero ((j)^*[ModuleCat.{u + 1} R].obj F)) : IsZero F := by
  let Y : Bool → Scheme.{u} := fun b ↦ bif b then Z else U
  let g : ∀ b, Y b ⟶ X := fun b ↦ match b with | true => i | false => j
  have : ∀ b, QuasiCompact (g b) := by rintro (_ | _) <;> dsimp [g] <;> infer_instance
  refine (IsZero.iff_id_eq_zero F).2 (eq_zero_of_forall_upperStar_map_eq_zero R g (fun x ↦ ?_)
    (𝟙 F) ?_)
  · by_cases hx : x ∈ Set.range i.base
    · exact ⟨true, hx⟩
    · exact ⟨false, hij.compl_eq ▸ hx⟩
  · rintro (_ | _)
    · exact hj.eq_of_src _ _
    · exact hi.eq_of_src _ _

omit [IsOpenImmersion j] in
/-- The restrictions to a closed immersion and to its quasi-compact open complement jointly
detect isomorphisms of pro-étale sheaves of modules: both restrictions are exact, so they
detect the vanishing of the kernel and the cokernel
(`AlgebraicGeometry.ProEtale.isZero_of_isZero_upperStar_of_isCompl`). -/
theorem isIso_of_isIso_upperStar_of_isCompl
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    {F G : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)} (φ : F ⟶ G)
    [IsIso ((i)^*[ModuleCat.{u + 1} R].map φ)] [IsIso ((j)^*[ModuleCat.{u + 1} R].map φ)] :
    IsIso φ := by
  have hker : ∀ {Y : Scheme.{u}} (g : Y ⟶ X) [IsIso ((g)^*[ModuleCat.{u + 1} R].map φ)],
      IsZero ((g)^*[ModuleCat.{u + 1} R].obj (kernel φ)) := fun g _ ↦
    (isZero_kernel_of_mono ((g)^*[ModuleCat.{u + 1} R].map φ)).of_iso
      (PreservesKernel.iso _ φ)
  have hcoker : ∀ {Y : Scheme.{u}} (g : Y ⟶ X) [IsIso ((g)^*[ModuleCat.{u + 1} R].map φ)],
      IsZero ((g)^*[ModuleCat.{u + 1} R].obj (cokernel φ)) := fun g _ ↦
    (isZero_cokernel_of_epi ((g)^*[ModuleCat.{u + 1} R].map φ)).of_iso
      (PreservesCokernel.iso _ φ)
  have : Mono φ := Preadditive.mono_of_isZero_kernel _
    (isZero_of_isZero_upperStar_of_isCompl i j hij _ (hker i) (hker j))
  have : Epi φ := Preadditive.epi_of_isZero_cokernel _
    (isZero_of_isZero_upperStar_of_isCompl i j hij _ (hcoker i) (hcoker j))
  exact isIso_of_mono_of_epi φ

/-- The pushforward along a closed immersion with quasi-compact open complement preserves
epimorphisms of pro-étale sheaves of modules. For an epimorphism `φ`, the cokernel of
`i_* φ` restricts to zero on `Z`, because `i^* i_* φ` is `φ` up to the counit isomorphism, and
on `U`, because `j^* i_* = 0`. -/
lemma epi_lowerStar_map_of_isCompl (hij : IsCompl (Set.range i.base) (Set.range j.base))
    {G H : Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} R)} (φ : G ⟶ H) [Epi φ] :
    Epi ((i)_*[ModuleCat.{u + 1} R].map φ) := by
  set ε := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).counit
  have hε : (i)^*[ModuleCat.{u + 1} R].map ((i)_*[ModuleCat.{u + 1} R].map φ) =
      ε.app G ≫ φ ≫ inv (ε.app H) := by
    rw [← Category.assoc, IsIso.eq_comp_inv]
    exact ε.naturality φ
  have : Epi ((i)^*[ModuleCat.{u + 1} R].map ((i)_*[ModuleCat.{u + 1} R].map φ)) := by
    rw [hε]
    infer_instance
  refine Preadditive.epi_of_isZero_cokernel _
    (isZero_of_isZero_upperStar_of_isCompl i j hij _ ?_ ?_)
  · exact (isZero_cokernel_of_epi _).of_iso (PreservesCokernel.iso _ _)
  · exact (IsZero.of_epi (cokernel.π _) (isZero_upperStar_lowerStar_of_disjoint _ i j
      hij.disjoint H)).of_iso (PreservesCokernel.iso _ _)

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme--4`: let `i : Z ⟶ X` be a
closed immersion whose complementary open immersion `j` is quasi-compact. Then `i_*` is exact on
pro-étale sheaves of modules. It is left exact as a right adjoint, and it preserves epimorphisms by
`AlgebraicGeometry.ProEtale.epi_lowerStar_map_of_isCompl`. -/
theorem preservesFiniteColimits_lowerStar_of_isCompl
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) :
    PreservesFiniteColimits ((i)_*[ModuleCat.{u + 1} R]) := by
  have : ((i)_*[ModuleCat.{u + 1} R]).PreservesEpimorphisms :=
    ⟨fun φ _ ↦ epi_lowerStar_map_of_isCompl i j hij φ⟩
  have := Functor.preservesHomology_of_preservesEpis_and_kernels ((i)_*[ModuleCat.{u + 1} R])
  exact Functor.preservesFiniteColimits_of_preservesHomology _

/-- Blueprint `lemma-passing-schematic-closure--1`, the unit: let `i : Z ⟶ X` be a closed
immersion with quasi-compact open complement `j`. For a pro-étale sheaf of modules `F` with
`j^* F = 0`, the unit `F ⟶ i_* i^* F` is an isomorphism. Its restriction to `Z` is inverse to the
counit isomorphism by a triangle identity, and its restriction to `U` is a map between zero
objects, so `AlgebraicGeometry.ProEtale.isIso_of_isIso_upperStar_of_isCompl` applies. -/
theorem isIso_upperStarLowerStarAdjunction_unit_app_of_isCompl
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R))
    (hF : IsZero ((j)^*[ModuleCat.{u + 1} R].obj F)) :
    IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).unit.app F) := by
  set adj := upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i
  have : IsIso ((i)^*[ModuleCat.{u + 1} R].map (adj.unit.app F)) := by
    have h := adj.left_triangle_components F
    have : IsIso ((i)^*[ModuleCat.{u + 1} R].map (adj.unit.app F) ≫
        adj.counit.app ((i)^*[ModuleCat.{u + 1} R].obj F)) := by
      rw [h]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right _ (adj.counit.app _)
  have : IsIso ((j)^*[ModuleCat.{u + 1} R].map (adj.unit.app F)) :=
    ⟨⟨0, hF.eq_of_src _ _, (isZero_upperStar_lowerStar_of_disjoint _ i j hij.disjoint
      _).eq_of_src _ _⟩⟩
  exact isIso_of_isIso_upperStar_of_isCompl i j hij _

/-- Blueprint `lemma-passing-schematic-closure--1`: let `i : Z ⟶ X` be a closed immersion
with quasi-compact open complement `j`. A pro-étale sheaf of modules `F` on `X` lies in the
essential image of `i_*` if and only if `j^* F = 0`. -/
theorem lowerStar_essImage_iff_of_isCompl
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) :
    ((i)_*[ModuleCat.{u + 1} R]).essImage F ↔ IsZero ((j)^*[ModuleCat.{u + 1} R].obj F) := by
  constructor
  · rintro ⟨G, ⟨e⟩⟩
    exact (isZero_upperStar_lowerStar_of_disjoint _ i j hij.disjoint G).of_iso
      ((j)^*[ModuleCat.{u + 1} R].mapIso e.symm)
  · intro hF
    have := isIso_upperStarLowerStarAdjunction_unit_app_of_isCompl i j hij F hF
    exact ⟨_, ⟨(asIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) i).unit.app F)).symm⟩⟩


end ProEtale

end AlgebraicGeometry
