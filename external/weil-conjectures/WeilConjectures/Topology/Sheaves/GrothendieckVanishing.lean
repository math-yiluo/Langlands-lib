/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sober
public import WeilConjectures.Topology.Sheaves.NoetherianColimit
public import WeilConjectures.Topology.Sheaves.SectionSupport

/-!
# Grothendieck vanishing

Let `X` be a noetherian topological space of dimension `d` in which every irreducible closed
subset has a generic point (for instance the underlying space of a noetherian scheme). Then
`Hᵠ(X, F) = 0` for every abelian sheaf `F` on `X` and every `q > d`
(`TopCat.Sheaf.subsingleton_H_of_topologicalKrullDim_lt`, blueprint
`lemma-uniform-bounds-pro-etale-affines`).
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

section Supported

variable {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}

/-- An abelian sheaf `F` on `X` is supported in `Z`: the support of every section of `F` is
contained in `Z`. -/
def IsSupportedIn (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (Z : Set X) : Prop :=
  ∀ ⦃V : Opens X⦄ (s : F.obj.obj (op V)), sectionSupport F s ⊆ Z

lemma IsSupportedIn.isZero (hF : IsSupportedIn F ∅) : IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  ext V s
  exact eq_zero_of_sectionSupport_eq_empty s (Set.subset_empty_iff.1 (hF s))

/-- The cohomology of a zero abelian sheaf vanishes. -/
lemma subsingleton_H_of_isZero (hF : IsZero F) (n : ℕ) : Subsingleton (Sheaf.H F n) :=
  ⟨fun x y ↦ by
    rw [← Sheaf.H.map_id_apply x, ← Sheaf.H.map_id_apply y, hF.eq_of_src (𝟙 F) 0,
      Sheaf.H.map_apply, Sheaf.H.map_apply]
    simp⟩

/-- If `ψ : F ⟶ Q` has a retraction and `Hⁿ(ψ)` vanishes, then `Hⁿ(F) = 0`. -/
lemma subsingleton_H_of_comp_eq_id {Q : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}} {ψ : F ⟶ Q} {φ : Q ⟶ F} (hψ : ψ ≫ φ = 𝟙 F) {n : ℕ}
    (h : ∀ x : Sheaf.H F n, Sheaf.H.map ψ n x = 0) : Subsingleton (Sheaf.H F n) :=
  subsingleton_of_forall_eq 0 fun x ↦ by
    rw [← Sheaf.H.map_id_apply x, ← hψ, Sheaf.H.map_comp_apply, h, map_zero]

/-- A map of abelian sheaves induces the zero map on `Hⁿ` when `Hⁿ` of its source vanishes. -/
lemma H_map_eq_zero_of_subsingleton (f : F ⟶ G) {n : ℕ} (h : Subsingleton (Sheaf.H F n))
    (y : Sheaf.H F n) : Sheaf.H.map f n y = 0 := by
  rw [h.elim y 0, map_zero]

/-- If `f ≫ g = 0`, then `g` kills the image under `f` of every section. -/
lemma app_app_eq_zero_of_comp_eq_zero {H : CategoryTheory.Sheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}} {f : F ⟶ G} {g : G ⟶ H} (h : f ≫ g = 0) {V : Opens X}
    (t : F.obj.obj (op V)) : g.hom.app (op V) (f.hom.app (op V) t) = 0 := by
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
    ← ObjectProperty.FullSubcategory.comp_hom, h]
  rfl

lemma kernel_ι_app_apply (ψ : F ⟶ G) {V : Opens X} (t : (kernel ψ).obj.obj (op V)) :
    ψ.hom.app (op V) ((kernel.ι ψ).hom.app (op V) t) = 0 :=
  app_app_eq_zero_of_comp_eq_zero (kernel.condition ψ) t

/-- A morphism of abelian sheaves vanishing on all sections is zero. -/
lemma eq_zero_of_app_eq_zero {f : F ⟶ G}
    (h : ∀ (V : Opens X) (s : F.obj.obj (op V)), f.hom.app (op V) s = 0) : f = 0 := by
  ext V s
  exact (h V.unop s).trans rfl

lemma sectionSupport_kernel_ι (ψ : F ⟶ G) {V : Opens X} (t : (kernel ψ).obj.obj (op V)) :
    sectionSupport (kernel ψ) t = sectionSupport F ((kernel.ι ψ).hom.app (op V) t) :=
  (sectionSupport_map_of_injective _ (injective_app_of_mono _) t).symm

end Supported

section Colimit

variable (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

/-- The subsheaf `F_Z ⊆ F` of the sections of `F` supported in `Z`: the kernel of the map from
`F` to the product of its stalks at the points off `Z`. -/
noncomputable abbrev supportedIn (Z : Set X) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  kernel (toGodementOn Zᶜ F)

lemma isSupportedIn_supportedIn (Z : Set X) : IsSupportedIn (supportedIn F Z) Z := by
  intro V t x hx
  rw [sectionSupport_kernel_ι] at hx
  by_contra hxZ
  exact (toGodementOn_app_eq_zero_iff _).1 (kernel_ι_app_apply _ t) x hxZ hx

variable {F} in
lemma toGodementOn_app_eq_zero_of_subset {Z : Set X} {V : Opens X} (s : F.obj.obj (op V))
    (hs : sectionSupport F s ⊆ Z) : (toGodementOn Zᶜ F).hom.app (op V) s = 0 :=
  (toGodementOn_app_eq_zero_iff s).2 fun _ hx hxs ↦ hx (hs hxs)

/-- The inclusion `F_Z ⟶ F_Z'` for `Z ⊆ Z'`. -/
noncomputable def supportedInMap {Z Z' : Set X} (h : Z ⊆ Z') :
    supportedIn F Z ⟶ supportedIn F Z' :=
  kernel.lift _ (kernel.ι _) (eq_zero_of_app_eq_zero fun V t ↦ by
    rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ConcreteCategory.comp_apply]
    refine toGodementOn_app_eq_zero_of_subset _ ?_
    rw [← sectionSupport_kernel_ι]
    exact (isSupportedIn_supportedIn F Z t).trans h)

@[reassoc (attr := simp)]
lemma supportedInMap_ι {Z Z' : Set X} (h : Z ⊆ Z') :
    supportedInMap F h ≫ kernel.ι _ = kernel.ι _ :=
  kernel.lift_ι _ _ _

/-- The diagram `Z ↦ F_Z` of the subsheaves of sections supported in the members of a family
`𝒵` of subsets of `X`. -/
@[simps]
noncomputable def supportedInFunctor (𝒵 : Set (Set X)) :
    𝒵 ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} where
  obj Z := supportedIn F Z.1
  map h := supportedInMap F (leOfHom h)
  map_id _ := (cancel_mono (kernel.ι _)).1 (by simp)
  map_comp _ _ := (cancel_mono (kernel.ι _)).1 (by simp)

variable [NoetherianSpace X]

/-- Let `𝒵` be a nonempty directed family of subsets of a noetherian space `X`, such that the
support of every section of `F` lies in some `Z ∈ 𝒵`. If `Hⁿ(X, F_Z) = 0` for all `Z ∈ 𝒵`, then
`Hⁿ(X, F) = 0`: `F` is the filtered colimit of the `F_Z`, and cohomology commutes with filtered
colimits on a noetherian space. -/
lemma subsingleton_H_of_directedOn {𝒵 : Set (Set X)} (hne : 𝒵.Nonempty)
    (hdir : DirectedOn (· ⊆ ·) 𝒵)
    (hF : ∀ ⦃V : Opens X⦄ (s : F.obj.obj (op V)), ∃ Z ∈ 𝒵, sectionSupport F s ⊆ Z) (n : ℕ)
    (hH : ∀ Z ∈ 𝒵, Subsingleton (Sheaf.H (supportedIn F Z) n)) : Subsingleton (Sheaf.H F n) := by
  have : Nonempty 𝒵 := hne.to_subtype
  have : IsDirectedOrder 𝒵 := ⟨fun a b ↦ by
    obtain ⟨c, hc, hac, hbc⟩ := hdir a.1 a.2 b.1 b.2
    exact ⟨⟨c, hc⟩, hac, hbc⟩⟩
  let D : 𝒵 ⥤ TopCat.Sheaf AddCommGrpCat.{u} X := supportedInFunctor F 𝒵
  let c : Cocone D :=
    { pt := F
      ι :=
        { app Z := kernel.ι (toGodementOn (Z.1)ᶜ F)
          naturality _ _ h := (supportedInMap_ι F (leOfHom h)).trans (Category.comp_id _).symm } }
  let φ : colimit D ⟶ F := colimit.desc D c
  have hφ (Z : 𝒵) {V : Opens X} (t : (supportedIn F Z.1).obj.obj (op V)) :
      φ.hom.app (op V) (((colimit.cocone D).ι.app Z).hom.app (op V) t) =
        (kernel.ι (toGodementOn (Z.1)ᶜ F)).hom.app (op V) t :=
    ConcreteCategory.congr_hom (congr_arg (fun f ↦ f.hom.app (op V)) (colimit.ι_desc c Z)) t
  have hbij (V : Opens X) : Function.Bijective (φ.hom.app (op V)) := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun s ↦ ?_⟩
    · obtain ⟨Z, t, rfl⟩ := exists_app_eq_of_isColimit (colimit.isColimit D) x
      obtain rfl : t = 0 := (injective_iff_map_eq_zero _).1
        (injective_app_of_mono (F := supportedIn F Z.1) (kernel.ι _) _) t
        ((hφ Z t).symm.trans hx)
      exact map_zero _
    · obtain ⟨Z, hZ, hs⟩ := hF s
      obtain ⟨t, rfl⟩ := exists_kernel_ι_app_eq _ s (toGodementOn_app_eq_zero_of_subset s hs)
      exact ⟨((colimit.cocone D).ι.app ⟨Z, hZ⟩).hom.app (op V) t, hφ ⟨Z, hZ⟩ t⟩
  have (V : (Opens X)ᵒᵖ) :
      IsIso (((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map φ).app V) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (hbij V.unop)
  have : IsIso ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map φ) :=
    NatIso.isIso_of_isIso_app _
  obtain ⟨ψ, -, hψ⟩ := ((fullyFaithfulSheafToPresheaf _ _).isIso_of_isIso_map φ).out
  refine subsingleton_H_of_comp_eq_id hψ fun x ↦ ?_
  obtain ⟨Z, y, hy⟩ := (hColimitProp n D).1 (Sheaf.H.map ψ n x)
  exact hy.symm.trans (H_map_eq_zero_of_subsingleton (colimit.ι D Z) (hH Z.1 Z.2) y)

end Colimit

section Vanishing

variable {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
  {Z : Set X} {E : Finset X}

/-- A section of a sheaf supported in a closed set `Z = ⋃_{η ∈ E} closure {η}` (with `E`
irredundant), whose germs vanish at the points of `E`, has its support in a closed subset of `Z`
containing no point of `E`. -/
lemma exists_closed_of_sectionSupport (hF : IsSupportedIn F Z) (hZ : IsClosed Z)
    (hZE : Z = ⋃ η ∈ E, closure {η}) (hE : ∀ η ∈ E, ∀ η' ∈ E, η ∈ closure {η'} → η = η')
    {V : Opens X} (s : F.obj.obj (op V)) (hs : ∀ η ∈ E, η ∉ sectionSupport F s) :
    ∃ Z' ∈ {Z' : Set X | IsClosed Z' ∧ Z' ⊆ Z ∧ ∀ η ∈ E, η ∉ Z'},
      sectionSupport F s ⊆ Z' := by
  refine ⟨closure (sectionSupport F s), ⟨isClosed_closure, closure_minimal (hF s) hZ,
    notMem_closure_of_subset hZE hE V.isOpen
      (fun x hx ↦ ⟨sectionSupport_subset s hx, hF s hx⟩) fun η hη hηV h ↦ ?_⟩, subset_closure⟩
  obtain ⟨W, hηW, hW⟩ := exists_disjoint_sectionSupport s hηV (hs η hη)
  obtain ⟨y, hyW, hyS⟩ := mem_closure_iff.1 h W W.isOpen hηW
  exact Set.disjoint_left.1 hW hyW hyS

/-- The sections of the cokernel of `F ⟶ godementOn E F` are supported in `Z ∖ E`, where
`Z = ⋃_{η ∈ E} closure {η}` is closed and `E` is irredundant. -/
lemma sectionSupport_cokernel_subset (hZ : IsClosed Z) (hZE : Z = ⋃ η ∈ E, closure {η})
    (hE : ∀ η ∈ E, ∀ η' ∈ E, η ∈ closure {η'} → η = η') {V : Opens X}
    (c : (cokernel (toGodementOn (E : Set X) F)).obj.obj (op V)) :
    sectionSupport _ c ⊆ Z \ E := by
  classical
  intro x ⟨hxV, hx⟩
  by_contra hxZE
  refine hx ((germ_eq_zero_iff c hxV).2 ?_)
  obtain ⟨W, hxW, i, g, hg⟩ := exists_mem_forall_exists_app_eq_of_epi (cokernel.π _) c hxV
  suffices ∃ (W' : Opens X) (_ : x ∈ W') (i' : W' ⟶ W) (s : F.obj.obj (op W')),
      (toGodementOn (E : Set X) F).hom.app (op W') s = (godementOn (E : Set X) F).obj.map i'.op g by
    obtain ⟨W', hxW', i', s, hs⟩ := this
    refine ⟨W', hxW', i' ≫ i, ?_⟩
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, ← hg,
      ← NatTrans.naturality_apply, ← hs]
    exact app_app_eq_zero_of_comp_eq_zero (cokernel.condition _) s
  have hEZ : (E : Set X) ⊆ Z := fun η hη ↦ hZE ▸ Set.mem_biUnion hη (subset_closure rfl)
  rcases not_and_or.1 hxZE with hxZ | hxE
  · refine ⟨W ⊓ ⟨Zᶜ, hZ.isOpen_compl⟩, ⟨hxW, hxZ⟩, homOfLE inf_le_left, 0, ?_⟩
    rw [map_zero]
    exact (godementOn_eq_zero (V := W ⊓ ⟨Zᶜ, hZ.isOpen_compl⟩) _
      (Set.disjoint_left.2 fun y hy hyE ↦ hy.2 (hEZ hyE))).symm
  rw [not_not] at hxE
  let T : Set X := ⋃ η' ∈ E.filter (fun η' ↦ x ∉ closure {η'}), closure {η'}
  have hT : IsClosed T :=
    (E.filter _).finite_toSet.isClosed_biUnion fun _ _ ↦ isClosed_closure
  have hxT : x ∉ T := fun h ↦ by
    obtain ⟨η', hη', hxη'⟩ := Set.mem_iUnion₂.1 h
    exact (Finset.mem_filter.1 hη').2 hxη'
  let W₁ : Opens X := W ⊓ ⟨Tᶜ, hT.isOpen_compl⟩
  let g₁ := (godementOn (E : Set X) F).obj.map (homOfLE inf_le_left : W₁ ⟶ W).op g
  obtain ⟨U, hxU, s, hs⟩ := TopCat.Presheaf.exists_germ_eq F.obj
    (g₁ ⟨x, hxW, hxT⟩ ⟨Finset.mem_coe.2 hxE⟩)
  refine ⟨U ⊓ W₁, ⟨hxU, hxW, hxT⟩, homOfLE inf_le_right ≫ homOfLE inf_le_left,
    F.obj.map (homOfLE inf_le_left : U ⊓ W₁ ⟶ U).op s, ?_⟩
  funext ⟨y, hyU, hyW, hyT⟩ ⟨hyE⟩
  obtain rfl : y = x := by
    refine (hE x hxE y hyE (by_contra fun h ↦ hyT ?_)).symm
    exact Set.mem_iUnion₂.2 ⟨y, Finset.mem_filter.2 ⟨hyE, h⟩, subset_closure rfl⟩
  rw [toGodementOn_app_apply, TopCat.Presheaf.germ_res_apply, hs]
  rfl

variable [NoetherianSpace X] [QuasiSober X]

/-- **Grothendieck vanishing for sheaves with small support**: on a noetherian quasi-sober
space, if `F` is supported in a closed set `Z` of dimension `< n`, then `Hᵠ(X, F) = 0` for all
`q ≥ n`. -/
theorem subsingleton_H_of_isSupportedIn (n : ℕ) :
    ∀ (Z : Set X), IsClosed Z → DimLT Z n →
      ∀ (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}),
        IsSupportedIn F Z → ∀ q, n ≤ q → Subsingleton (Sheaf.H F q) := by
  induction n with
  | zero =>
    intro Z hZ hd F hF q _
    rw [eq_empty_of_dimLT_zero hd hZ] at hF
    exact subsingleton_H_of_isZero hF.isZero q
  | succ n ih =>
    intro Z hZ hd F hF q hq
    obtain ⟨E, hZE, hE⟩ := exists_finset_irredundant hZ
    let 𝒵 : Set (Set X) := {Z' | IsClosed Z' ∧ Z' ⊆ Z ∧ ∀ η ∈ E, η ∉ Z'}
    have hne : 𝒵.Nonempty := ⟨∅, isClosed_empty, Set.empty_subset _, fun _ _ h ↦ h⟩
    have hdir : DirectedOn (· ⊆ ·) 𝒵 := fun A hA B hB ↦ ⟨A ∪ B, ⟨hA.1.union hB.1,
      Set.union_subset hA.2.1 hB.2.1, fun η hη h ↦ h.elim (hA.2.2 η hη) (hB.2.2 η hη)⟩,
      Set.subset_union_left, Set.subset_union_right⟩
    have h𝒵 (G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
        (hG : ∀ ⦃V : Opens X⦄ (s : G.obj.obj (op V)), ∃ Z' ∈ 𝒵, sectionSupport G s ⊆ Z')
        (p : ℕ) (hp : n ≤ p) : Subsingleton (Sheaf.H G p) :=
      subsingleton_H_of_directedOn G hne hdir hG p fun Z' hZ' ↦
        ih Z' hZ'.1 (hd.of_subset_of_forall_notMem hZE hZ'.2.1 hZ'.2.2) _
          (isSupportedIn_supportedIn G Z') p hp
    let φ := toGodementOn (E : Set X) F
    let g := Abelian.factorThruImage φ
    let S₁ := ShortComplex.mk (kernel.ι g) g (kernel.condition g)
    have hS₁ : S₁.ShortExact := ShortComplex.ShortExact.mk'
      (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel g)) inferInstance inferInstance
    let S₂ := ShortComplex.mk (Abelian.image.ι φ) (cokernel.π φ) (kernel.condition _)
    have hS₂ : S₂.ShortExact := ShortComplex.ShortExact.mk'
      (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)) inferInstance inferInstance
    obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    have hKs ⦃V : Opens X⦄ (t : (kernel g).obj.obj (op V)) :
        ∃ Z' ∈ 𝒵, sectionSupport (kernel g) t ⊆ Z' := by
      rw [sectionSupport_kernel_ι]
      refine exists_closed_of_sectionSupport hF hZ hZE hE _ ?_
      have h0 : kernel.ι g ≫ φ = 0 :=
        (congrArg (kernel.ι g ≫ ·) (Abelian.image.fac φ : g ≫ Abelian.image.ι φ = φ).symm).trans
          (by rw [← Category.assoc, kernel.condition, zero_comp])
      exact (toGodementOn_app_eq_zero_iff _).1 (app_app_eq_zero_of_comp_eq_zero h0 t)
    have hCs ⦃V : Opens X⦄ (c : (cokernel φ).obj.obj (op V)) :
        ∃ Z' ∈ 𝒵, sectionSupport (cokernel φ) c ⊆ Z' :=
      exists_closed_of_sectionSupport
        (fun _ c' ↦ (sectionSupport_cokernel_subset hZ hZE hE c').trans Set.sdiff_subset)
        hZ hZE hE c fun η hη h ↦ (sectionSupport_cokernel_subset hZ hZE hE c h).2 hη
    have hK : Subsingleton (Sheaf.H (kernel g) (q + 1)) := h𝒵 _ hKs _ (by omega)
    have hC : Subsingleton (Sheaf.H (cokernel φ) q) := h𝒵 _ hCs _ (by omega)
    have hG : Subsingleton (Sheaf.H S₂.X₂ (q + 1)) :=
      IsFlasque.subsingleton_H q (godementOn (E : Set X) F)
    have hI : Subsingleton (Sheaf.H (Abelian.image φ) (q + 1)) := by
      refine subsingleton_of_forall_eq 0 fun x ↦ ?_
      obtain ⟨y, rfl⟩ := Sheaf.H.δSucc_surjective hS₂ q x
      rw [Subsingleton.elim y 0, map_zero]
    refine subsingleton_of_forall_eq 0 fun x ↦ ?_
    obtain ⟨y, hy⟩ := (Sheaf.H.exact_map_map hS₁ (q + 1) x).1 (Subsingleton.elim _ _)
    rw [← hy, Subsingleton.elim y 0, map_zero]

end Vanishing


/-- Blueprint `lemma-uniform-bounds-pro-etale-affines`: The Zariski dimension bound (Grothendieck
vanishing).

Let `X` be a noetherian topological space of dimension at most `d`, in which every irreducible
closed subset has a generic point. Then `Hᵠ(X, F) = 0` for every abelian sheaf `F` on `X` and
every `q > d`. The blueprint states this for the underlying space of a noetherian scheme, which
is quasi-sober (`AlgebraicGeometry.Scheme.subsingleton_H_of_topologicalKrullDim_lt`). -/
@[stacks 02UZ]
theorem subsingleton_H_of_topologicalKrullDim_lt [NoetherianSpace X] [QuasiSober X]
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) {q : ℕ}
    (hq : topologicalKrullDim X < q) : Subsingleton (Sheaf.H F q) :=
  subsingleton_H_of_isSupportedIn q Set.univ isClosed_univ
    (dimLT_of_topologicalKrullDim_lt hq _) F (fun _ _ ↦ Set.subset_univ _) q le_rfl

end TopCat.Sheaf
