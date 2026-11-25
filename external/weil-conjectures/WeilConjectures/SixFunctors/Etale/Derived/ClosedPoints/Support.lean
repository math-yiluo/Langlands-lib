/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.GlobalGeneration
public import WeilConjectures.AlgebraicGeometry.Sites.FilteredColimitSections
public import WeilConjectures.AlgebraicGeometry.ClosedPointResidueField
public import WeilConjectures.AlgebraicGeometry.Sites.UpperStarSections

/-!
# Étale sheaves supported on the closed points

Let `X` be a scheme locally of finite type over a separably closed field `K`, and `F` an étale
sheaf of `Λ`-modules on `X` whose geometric stalks vanish at all non-closed points. A section
`z` of `F` over a quasi-compact étale `X`-scheme `W` vanishes outside the preimage of a finite
set `S` of closed points of `X`: the locus where `z` does not vanish is closed, and its
irreducible components have generic points lying over closed points. So `z` is a section of the
subsheaf `F_S = ker(F ⟶ j_* j^* F)` of sections supported on `S`, `j` the inclusion of the
complement of `S`. The sheaves `F_S` are globally generated
(`AlgebraicGeometry.Etale.isGloballyGenerated_of_isZero_upperStar`), and they cover `F`.

## Main definitions

- `AlgebraicGeometry.Etale.sectionVanishingLocus`: the open set where a section vanishes.
- `AlgebraicGeometry.Etale.supportedSections`: the subsheaf of sections supported in the
  complement of an open subscheme.

## Main statements

- `AlgebraicGeometry.Etale.exists_finite_forall_mem_sectionVanishingLocus`: a section over a
  quasi-compact étale `X`-scheme is supported over finitely many closed points.
- `AlgebraicGeometry.Etale.isGloballyGenerated_of_isZero_sheafFiber`
(`corollary-open-direct-image-over-field--2`):
  `F` is globally generated.
- `AlgebraicGeometry.Etale.isZero_of_isZero_sheafFiber_of_subsingleton`: if moreover `F` has
  no nonzero global sections, then `F = 0`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Topology

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

section VanishingLocus

variable {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))

/-- The vanishing locus of a section `z` of an étale sheaf `F` of `Λ`-modules over an étale
`X`-scheme `W`: the points of `W` near which `z` vanishes étale locally. -/
def sectionVanishingLocus {W : X.Etale} (z : F.obj.obj (op W)) : Set W.left :=
  {w | ∃ (V : X.Etale) (b : V ⟶ W), w ∈ Set.range b.left ∧ F.obj.map b.op z = 0}

variable {F}

/-- The vanishing locus of a section is open, étale morphisms being open. -/
lemma isOpen_sectionVanishingLocus {W : X.Etale} (z : F.obj.obj (op W)) :
    IsOpen (sectionVanishingLocus F z) := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨V, b, hx, hz⟩
  have := etale_left b
  refine ⟨Set.range b.left, ?_, b.left.isOpenMap.isOpen_range, hx⟩
  rintro _ ⟨v, rfl⟩
  exact ⟨V, b, ⟨v, rfl⟩, hz⟩

/-- A section whose vanishing locus is everything vanishes. -/
lemma eq_zero_of_forall_mem_sectionVanishingLocus {W : X.Etale} {z : F.obj.obj (op W)}
    (h : ∀ w, w ∈ sectionVanishingLocus F z) : z = 0 := by
  choose V b hb hz using h
  have hcov : ⋃ w, Set.range (b w).left = Set.univ :=
    Set.iUnion_eq_univ_iff.2 fun w ↦ ⟨w, hb w⟩
  exact (Scheme.isSheafFor_ofArrows_moduleCat F b hcov).isSeparatedFor.ext fun _ _ ⟨w⟩ ↦
    by simp [hz w]

/-- A point whose image lies in the vanishing locus of `z` lies in the vanishing locus of the
restriction of `z`. -/
lemma mem_sectionVanishingLocus_map {W W' : X.Etale} (c : W' ⟶ W) {z : F.obj.obj (op W)}
    {v : W'.left} (hv : c.left v ∈ sectionVanishingLocus F z) :
    v ∈ sectionVanishingLocus F (F.obj.map c.op z) := by
  obtain ⟨V, b, ⟨w, hw⟩, hz⟩ := hv
  obtain ⟨p, hp₁, -⟩ := Scheme.Pullback.exists_preimage_pullback v w hw.symm
  have hcomm : overlapFst c b ≫ c = overlapSnd c b ≫ b :=
    MorphismProperty.Over.Hom.ext (by simp [pullback.condition])
  refine ⟨overlap c b, overlapFst c b, ⟨p, by simpa using hp₁⟩, ?_⟩
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hcomm, op_comp,
    Functor.map_comp, ConcreteCategory.comp_apply, hz, map_zero]

end VanishingLocus

section FiniteSupport

variable {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))

/-- **A section is supported over finitely many closed points.** Let `X` be locally of finite
type over a field, `F` an étale sheaf of `Λ`-modules on `X` whose stalks at the geometric points
over non-closed points vanish, and `z` a section of `F` over an étale `X`-scheme `W` with
quasi-compact underlying space. Then there is a finite set `S` of closed points of `X` such that
`z` vanishes near every point of `W` not lying over `S`.

A point `w` of `W` near which `z` does not vanish lies over a closed point: otherwise the germ
of `z` at a geometric point over `w` lies in a vanishing stalk
(`AlgebraicGeometry.Etale.toPresheafFiber_eq_zero_iff`). The locus of such points is closed in
the Noetherian space `W`, hence a finite union of irreducible closed sets, and each of these
maps to the closure of the image of its generic point, a closed point. -/
theorem exists_finite_forall_mem_sectionVanishingLocus {K : Type u} [Field K]
    (p : X ⟶ Spec (.of K)) [LocallyOfFiniteType p]
    (hF : ∀ x ∉ closedPoints X,
      IsZero ((pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj F))
    {W : X.Etale} [CompactSpace W.left] (z : F.obj.obj (op W)) :
    ∃ S : Set X, S.Finite ∧ S ⊆ closedPoints X ∧
      ∀ w : W.left, W.hom w ∉ S → w ∈ sectionVanishingLocus F z := by
  -- the points near which `z` does not vanish lie over closed points
  have hcl (w : W.left) (hw : w ∉ sectionVanishingLocus F z) : W.hom w ∈ closedPoints X := by
    by_contra hx
    apply hw
    obtain ⟨l, hl, hlw⟩ := exists_fac_of_etale_of_isSepClosed W.hom
      (X.algClosurePoint (W.hom w)) w (by simp)
    have h0 : (pointSmallEtale (X.algClosurePoint (W.hom w))).toPresheafFiber W
        (Over.homMk l hl) F.obj z = 0 :=
      (ModuleCat.isZero_iff_subsingleton.1 (hF _ hx)).elim _ _
    obtain ⟨V, b, hb, hz⟩ := (toPresheafFiber_eq_zero_iff F _ z).1 h0
    exact ⟨V, b, hlw ▸ hb, hz⟩
  -- `W` is a Noetherian space
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : Etale W.hom := W.prop
  have : IsLocallyNoetherian W.left := LocallyOfFiniteType.isLocallyNoetherian (W.hom ≫ p)
  have : IsNoetherian W.left := {}
  let Z : Set W.left := (sectionVanishingLocus F z)ᶜ
  have hZ : IsClosed Z := (isOpen_sectionVanishingLocus z).isClosed_compl
  obtain ⟨T, hTf, hTc, hTi, hZT⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  have : Finite T := hTf.to_subtype
  let η (t : T) : W.left := (hTi t.1 t.2).genericPoint
  have hη (t : T) : closure {η t} = t.1 := by
    rw [IsIrreducible.genericPoint_closure_eq, (hTc t.1 t.2).closure_eq]
  have hηZ (t : T) : η t ∈ Z := by
    rw [hZT]
    exact ⟨t.1, t.2, hη t ▸ subset_closure rfl⟩
  refine ⟨Set.range fun t ↦ W.hom (η t), Set.finite_range _, ?_, fun w hw ↦ ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact hcl _ (hηZ t)
  · by_contra hwZ
    obtain ⟨t, ht, hwt⟩ : ∃ t ∈ T, w ∈ t := by
      have : w ∈ Z := hwZ
      rw [hZT] at this
      exact this
    have hclosed : IsClosed ({W.hom (η ⟨t, ht⟩)} : Set X) := hcl _ (hηZ _)
    have h1 : W.hom w ∈ W.hom '' closure {η ⟨t, ht⟩} :=
      ⟨w, (hη ⟨t, ht⟩).symm ▸ hwt, rfl⟩
    have h2 := image_closure_subset_closure_image W.hom.continuous h1
    rw [Set.image_singleton, hclosed.closure_eq] at h2
    exact hw ⟨⟨t, ht⟩, h2.symm⟩

end FiniteSupport
section SupportedSections

variable {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))

/-- A section of an étale sheaf of `Λ`-modules which is killed by a morphism lifts to the
kernel. -/
lemma exists_kernel_ι_hom_app_eq {G H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (ψ : G ⟶ H) {W : X.Etale} (x : G.obj.obj (op W)) (hx : ψ.hom.app (op W) x = 0) :
    ∃ t : (kernel ψ).obj.obj (op W), (kernel.ι ψ).hom.app (op W) t = x := by
  let E := sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
    (CategoryTheory.evaluation _ _).obj (op W)
  let e := PreservesKernel.iso E ψ ≪≫ ModuleCat.kernelIsoKer (E.map ψ)
  refine ⟨e.inv ⟨x, hx⟩, ?_⟩
  have h₁ := PreservesKernel.iso_inv_ι E ψ
  have h₂ := ModuleCat.kernelIsoKer_inv_kernel_ι (E.map ψ)
  change (e.inv ≫ E.map (kernel.ι ψ)) ⟨x, hx⟩ = x
  rw [Iso.trans_inv, Category.assoc, h₁, h₂]
  rfl

/-- The subsheaf `F_Z = ker(F ⟶ j_* j^* F)` of the sections of `F` supported in the closed
complement `Z` of an open `U` of `X`, where `j : U ⟶ X` is the inclusion and `j^*` is the
restriction `AlgebraicGeometry.Etale.openImmersionRestriction`. -/
noncomputable def supportedSections (U : X.Opens) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  kernel ((openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} Λ) U.ι).unit.app F)

/-- The inclusion `F_Z ⟶ F` of the sections supported in the complement of `U`. -/
noncomputable def supportedSectionsι (U : X.Opens) : supportedSections F U ⟶ F :=
  kernel.ι _

@[reassoc (attr := simp)]
lemma supportedSectionsι_comp_unit (U : X.Opens) :
    supportedSectionsι F U ≫
      (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} Λ) U.ι).unit.app F = 0 :=
  kernel.condition _

instance (U : X.Opens) : Mono (supportedSectionsι F U) := by
  dsimp [supportedSectionsι]
  infer_instance

/-- The sheaf of sections supported in the complement of `U` vanishes on `U`: the restriction
to `U` of the unit `F ⟶ j_* j^* F` is invertible, the counit of `j^* ⊣ j_*` being invertible. -/
lemma isZero_upperStar_supportedSections (U : X.Opens) :
    IsZero ((U.ι)^*[ModuleCat.{u + 1} Λ].obj (supportedSections F U)) := by
  let adj := openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} Λ) U.ι
  let R := openImmersionRestriction (ModuleCat.{u + 1} Λ) U.ι
  have : IsIso (R.map (adj.unit.app F)) := by
    have : IsIso (R.map (adj.unit.app F) ≫ adj.counit.app (R.obj F)) := by
      rw [adj.left_triangle_components F]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right _ (adj.counit.app (R.obj F))
  let P := (U.ι)^*[ModuleCat.{u + 1} Λ]
  have : IsIso (P.map (adj.unit.app F)) :=
    (NatIso.isIso_map_iff (upperStarIsoOpenImmersionRestriction _ U.ι) _).2 this
  have hmono : Mono (P.map (supportedSectionsι F U)) := Functor.map_mono P _
  have hm : Mono (P.map (adj.unit.app F)) := IsIso.mono_of_iso _
  have h1 : P.map (supportedSectionsι F U) ≫ P.map (adj.unit.app F) =
      0 ≫ P.map (adj.unit.app F) := by
    rw [← P.map_comp, supportedSectionsι_comp_unit, P.map_zero, zero_comp]
  have h0 : P.map (supportedSectionsι F U) = 0 :=
    (@cancel_mono _ _ _ _ _ (P.map (adj.unit.app F)) hm _ _).1 h1
  exact @IsZero.of_mono_eq_zero _ _ _ _ _ _ hmono h0

/-- The unit `F ⟶ j_* j^* F` on sections over `W` is the restriction to `W ×_X U`. -/
lemma openImmersionRestrictionLowerStarAdjunction_ι_unit_app_hom_app (U : X.Opens)
    (W : X.Etale) :
    ((openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} Λ) U.ι).unit.app
        F).hom.app (op W) =
      F.obj.map ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ U.ι inferInstance
        trivial).counit.app W).op :=
  rfl

/-- A section `z` of `F` over `W` which vanishes near every point of `W` lying over `U` is a
section of the subsheaf `F_Z` of sections supported in the complement of `U`. -/
lemma exists_supportedSectionsι_app_eq (U : X.Opens) {W : X.Etale} (z : F.obj.obj (op W))
    (hz : ∀ w : W.left, W.hom w ∈ U → w ∈ sectionVanishingLocus F z) :
    ∃ z', (supportedSectionsι F U).hom.app (op W) z' = z := by
  refine exists_kernel_ι_hom_app_eq _ z ?_
  rw [openImmersionRestrictionLowerStarAdjunction_ι_unit_app_hom_app]
  let c := (MorphismProperty.Over.mapPullbackAdj @Etale ⊤ U.ι inferInstance trivial).counit.app W
  have key : F.obj.map c.op z = 0 := by
    refine eq_zero_of_forall_mem_sectionVanishingLocus (F := F) fun v ↦
      mem_sectionVanishingLocus_map c (hz _ ?_)
    have h := MorphismProperty.Over.w c
    have h' := congrArg (fun f ↦ f v) h
    simp only [Scheme.Hom.comp_apply] at h'
    have h'' : W.hom (c.left v) = _ := h'
    rw [h'', ← SetLike.mem_coe, ← Scheme.Opens.range_ι]
    exact ⟨_, rfl⟩
  exact key

end SupportedSections

section GlobalGeneration

variable {K : Type u} [Field K] [IsSepClosed K] {X : Scheme.{u}}
  (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))

/-- The open complement of a finite set of closed points. -/
def openComplOfFinite {S : Set X} (hS : S.Finite) (hS' : S ⊆ closedPoints X) : X.Opens :=
  ⟨Sᶜ, isOpen_compl_iff.mpr (by
    rw [← Set.biUnion_of_singleton S]
    exact hS.isClosed_biUnion fun x hx ↦ hS' hx)⟩

lemma coe_openComplOfFinite {S : Set X} (hS : S.Finite) (hS' : S ⊆ closedPoints X) :
    (openComplOfFinite hS hS' : Set X) = Sᶜ :=
  rfl

omit [IsSepClosed K] in
/-- **The sheaves of sections supported on finite sets of closed points cover `F`.** Under the
hypotheses of `AlgebraicGeometry.Etale.exists_finite_forall_mem_sectionVanishingLocus`, every
section of `F` is, étale locally, a section of the subsheaf `F_S` of sections supported on some
finite set `S` of closed points. -/
theorem exists_supportedSectionsι_app_eq_map (p : X ⟶ Spec (.of K)) [LocallyOfFiniteType p]
    (hF : ∀ x ∉ closedPoints X,
      IsZero ((pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj F))
    {W : X.Etale} (s : F.obj.obj (op W)) (w : W.left) :
    ∃ (V : X.Etale) (g : V ⟶ W), w ∈ Set.range g.left ∧ ∃ (S : Set X) (hS : S.Finite)
      (hS' : S ⊆ closedPoints X)
      (z : (supportedSections F (openComplOfFinite hS hS')).obj.obj (op V)),
        (supportedSectionsι F (openComplOfFinite hS hS')).hom.app (op V) z =
          F.obj.map g.op s := by
  obtain ⟨O', hO, hwO, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    W.left.isBasis_affineOpens) (show w ∈ (⊤ : W.left.Opens) from trivial)
  let O : W.left.Opens := O'
  have : Etale W.hom := W.prop
  let V : X.Etale := Scheme.Etale.mk (O.ι ≫ W.hom)
  let g : V ⟶ W := MorphismProperty.Over.homMk O.ι rfl
  have : IsAffine O := hO
  have : CompactSpace V.left := inferInstanceAs (CompactSpace O)
  obtain ⟨S, hSf, hSc, hS⟩ :=
    exists_finite_forall_mem_sectionVanishingLocus F p hF (F.obj.map g.op s)
  obtain ⟨z, hz⟩ := exists_supportedSectionsι_app_eq F (openComplOfFinite hSf hSc)
    (F.obj.map g.op s) fun v hv ↦ hS v hv
  exact ⟨V, g, ⟨⟨w, hwO⟩, rfl⟩, S, hSf, hSc, z, hz⟩

/-- Blueprint `corollary-open-direct-image-over-field--2`: **global generation for sheaves supported
on closed points.** Let `K` be a separably closed field, `X` a scheme locally of finite type over
`K` and `F` an étale sheaf of `Λ`-modules on `X` whose stalks at the geometric points over the
non-closed points of `X` vanish. Then `F` is globally generated.

For a finite set `S` of closed points (whose residue fields are separably closed,
`AlgebraicGeometry.Scheme.Hom.residueField_of_isClosed_of_isSepClosed`) the subsheaf `F_S` of
sections supported on `S` is globally generated
(`AlgebraicGeometry.Etale.isGloballyGenerated_of_isZero_upperStar`). Every section of `F` over
an affine étale `X`-scheme lies in some `F_S`
(`AlgebraicGeometry.Etale.exists_finite_forall_mem_sectionVanishingLocus`), so the `F_S` cover
`F` and `F` is globally generated (`AlgebraicGeometry.Etale.isGloballyGenerated_of_epi_sigmaDesc`).
The blueprint argues with the finitely generated subsheaves of `F` instead of the `F_S`. -/
theorem isGloballyGenerated_of_isZero_sheafFiber (p : X ⟶ Spec (.of K)) [LocallyOfFiniteType p]
    (hF : ∀ x ∉ closedPoints X,
      IsZero ((pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj F)) :
    IsGloballyGenerated Λ X F := by
  let ι := {S : Set X // S.Finite ∧ S ⊆ closedPoints X}
  let U (S : ι) : X.Opens := openComplOfFinite S.2.1 S.2.2
  let G (S : ι) := supportedSections F (U S)
  have : HasColimitsOfSize.{u + 1, u + 1} (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    IsGrothendieckAbelian.hasColimits _
  have : HasColimitsOfSize.{u, u} (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    hasColimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  have hG (S : ι) : IsGloballyGenerated Λ X (G S) := by
    refine isGloballyGenerated_of_isZero_upperStar Λ (U S) ?_ (fun x hx ↦ ?_) (fun x hx ↦ ?_)
      _ (isZero_upperStar_supportedSections F (U S))
    · simpa [U, ← SetLike.mem_coe, coe_openComplOfFinite] using S.2.1
    · have hx' : x ∈ S.1 := by simpa [U, ← SetLike.mem_coe, coe_openComplOfFinite] using hx
      exact S.2.2 hx'
    · have hx' : x ∈ S.1 := by simpa [U, ← SetLike.mem_coe, coe_openComplOfFinite] using hx
      exact (p.residueField_of_isClosed_of_isSepClosed x (S.2.2 hx')).2.2
  let ψ (S : ι) : G S ⟶ F := supportedSectionsι F (U S)
  have : Epi (Sigma.desc ψ) := by
    refine (Sheaf.isLocallySurjective_iff_epi' (ModuleCat.{u + 1} Λ) (Sigma.desc ψ)).1
      ⟨fun {W} s ↦ ?_⟩
    rw [mem_smallEtaleTopology_iff]
    intro w
    obtain ⟨V, g, hw, S, hSf, hSc, z, hz⟩ := exists_supportedSectionsι_app_eq_map F p hF s w
    refine ⟨V, g, ⟨(Sigma.ι G ⟨S, hSf, hSc⟩).hom.app (op V) z, ?_⟩, hw⟩
    rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
      ← ObjectProperty.FullSubcategory.comp_hom, Sigma.ι_comp_desc]
    exact hz
  exact isGloballyGenerated_of_epi_sigmaDesc Λ ψ hG

/-- An étale sheaf of `Λ`-modules on a scheme locally of finite type over a separably closed
field, with vanishing stalks at the non-closed points and without nonzero global sections, is
zero: it is globally generated (`corollary-open-direct-image-over-field--2`). -/
theorem isZero_of_isZero_sheafFiber_of_subsingleton (p : X ⟶ Spec (.of K)) [LocallyOfFiniteType p]
    (hF : ∀ x ∉ closedPoints X,
      IsZero ((pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj F))
    (h : Subsingleton (F.obj.obj (op (etaleTerminal X)))) : IsZero F :=
  isZero_of_isGloballyGenerated Λ (isGloballyGenerated_of_isZero_sheafFiber F p hF) h

end GlobalGeneration


end Etale

end AlgebraicGeometry
