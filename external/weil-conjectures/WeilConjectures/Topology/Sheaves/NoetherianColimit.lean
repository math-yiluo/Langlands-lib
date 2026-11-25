/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Topology.NoetherianSpace
public import WeilConjectures.Mathlib.Topology.Sheaves.Flasque
public import WeilConjectures.Topology.Sheaves.Godement

/-!
# Sheaf cohomology commutes with filtered colimits on a noetherian space

Let `X` be a noetherian topological space. Every open subset of `X` is quasi-compact, so a
filtered colimit of abelian sheaves on `X` is computed sectionwise
(`TopCat.Sheaf.isColimitSheafSectionsMapCocone`), a filtered colimit of flasque sheaves is
flasque (`TopCat.Sheaf.isFlasque_of_isColimit`), and sheaf cohomology `Hⁿ(X, -)` commutes with
filtered colimits (`TopCat.Sheaf.preservesColimitsOfShape_functorH`, blueprint
`lemma-uniform-bounds-pro-etale-affines`). The last statement follows by dimension shifting along
the functorial embedding of a sheaf into its Godement sheaf, which is flasque.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

section Sections

variable {X : TopCat.{u}} {J : Type u} [SmallCategory J]
  {D : J ⥤ TopCat.Sheaf AddCommGrpCat.{u} X} {c : Cocone D}

/-- The presheaf colimit of a diagram of sheaves, with its comparison map to the sheaf colimit:
the comparison is locally surjective and locally injective, being the sheafification map. -/
lemma exists_presheafColimit (hc : IsColimit c) :
    ∃ (E : Cocone (D ⋙ sheafToPresheaf _ _)) (_ : IsColimit E) (φ : E.pt ⟶ c.pt.obj),
      CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ ∧
      CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) φ ∧
      ∀ j, E.ι.app j ≫ φ = (c.ι.app j).hom := by
  let E := colimit.cocone (D ⋙ sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
  let hE : IsColimit E := colimit.isColimit _
  let e := (CategoryTheory.Sheaf.isColimitSheafifyCocone E hE).coconePointUniqueUpToIso hc
  refine ⟨E, hE, toSheafify _ E.pt ≫ e.hom.hom, ?_, ?_, fun k ↦ ?_⟩
  · infer_instance
  · infer_instance
  · rw [← Category.assoc, ← CategoryTheory.Sheaf.sheafifyCocone_ι_app_val,
      ← ObjectProperty.FullSubcategory.comp_hom,
      IsColimit.comp_coconePointUniqueUpToIso_hom]

/-- Sections of a colimit of sheaves are locally lifted: every section of `c.pt` over `U` is, on
the members of a covering sieve of `U`, the image of a section of some `D j`. -/
lemma exists_mem_forall_exists_app_eq [IsFiltered J] (hc : IsColimit c) {U : Opens X}
    (s : c.pt.obj.obj (op U)) :
    ∃ R ∈ Opens.grothendieckTopology X U, ∀ ⦃V : Opens X⦄ (f : V ⟶ U), R f →
      ∃ (j : J) (t : (D.obj j).obj.obj (op V)),
        (c.ι.app j).hom.app (op V) t = c.pt.obj.map f.op s := by
  obtain ⟨E, hE, φ, hs, -, hφ⟩ := exists_presheafColimit hc
  refine ⟨_, CategoryTheory.Presheaf.imageSieve_mem _ φ s, fun V f ⟨p, hp⟩ ↦ ?_⟩
  have hEV := isColimitOfPreserves ((CategoryTheory.evaluation _ _).obj (op V)) hE
  obtain ⟨k, t, rfl⟩ := Concrete.isColimit_exists_rep _ hEV p
  refine ⟨k, t, Eq.trans ?_ hp⟩
  rw [← hφ k]
  rfl

/-- Sections of a filtered colimit of sheaves are locally separated: two sections of `D j` over
`U` with the same image in `c.pt` agree, on the members of a covering sieve of `U`, in some
later `D j'`. -/
lemma exists_mem_forall_exists_map_eq [IsFiltered J] (hc : IsColimit c) {U : Opens X} {j : J}
    (t t' : (D.obj j).obj.obj (op U))
    (h : (c.ι.app j).hom.app (op U) t = (c.ι.app j).hom.app (op U) t') :
    ∃ R ∈ Opens.grothendieckTopology X U, ∀ ⦃V : Opens X⦄ (f : V ⟶ U), R f →
      ∃ (j' : J) (a : j ⟶ j'),
        (D.map a).hom.app (op V) ((D.obj j).obj.map f.op t) =
          (D.map a).hom.app (op V) ((D.obj j).obj.map f.op t') := by
  obtain ⟨E, hE, φ, -, hi, hφ⟩ := exists_presheafColimit hc
  have h' : φ.app (op U) ((E.ι.app j).app (op U) t) =
      φ.app (op U) ((E.ι.app j).app (op U) t') := by
    change (E.ι.app j ≫ φ).app _ t = (E.ι.app j ≫ φ).app _ t'
    rw [hφ]
    exact h
  refine ⟨_, CategoryTheory.Presheaf.equalizerSieve_mem _ φ _ _ h', fun V f hf ↦ ?_⟩
  have hEV := isColimitOfPreserves ((CategoryTheory.evaluation _ _).obj (op V)) hE
  have hf' : (E.ι.app j).app (op V) ((D.obj j).obj.map f.op t) =
      (E.ι.app j).app (op V) ((D.obj j).obj.map f.op t') := by
    have hn := (E.ι.app j).naturality f.op
    have e1 := ConcreteCategory.congr_hom hn t
    have e2 := ConcreteCategory.congr_hom hn t'
    simp only [ConcreteCategory.comp_apply] at e1 e2
    erw [e1, e2]
    exact hf
  obtain ⟨k', a, b, hab⟩ := Concrete.isColimit_exists_of_rep_eq _ hEV _ _ hf'
  refine ⟨_, a ≫ IsFiltered.coeqHom a b, ?_⟩
  let q := IsFiltered.coeqHom a b
  calc (D.map (a ≫ q)).hom.app (op V) ((D.obj j).obj.map f.op t)
      = (D.map q).hom.app (op V) ((D.map a).hom.app (op V) ((D.obj j).obj.map f.op t)) := by
        rw [D.map_comp]; rfl
    _ = (D.map q).hom.app (op V) ((D.map b).hom.app (op V) ((D.obj j).obj.map f.op t')) :=
        congrArg _ hab
    _ = (D.map (b ≫ q)).hom.app (op V) ((D.obj j).obj.map f.op t') := by
        rw [D.map_comp]; rfl
    _ = _ := by rw [← IsFiltered.coeq_condition a b]

omit [SmallCategory J] in
/-- A finite family of morphisms `aᵢ : j ⟶ jᵢ` out of an object of a filtered category extends to
a cocone: there are `A : j ⟶ j'` and `bᵢ : jᵢ ⟶ j'` with `aᵢ ≫ bᵢ = A`. -/
private lemma exists_comp_eq_of_finite' [Category J] [IsFiltered J] {j : J} {ι : Type*}
    [Finite ι] {j₁ : ι → J} (a : ∀ i, j ⟶ j₁ i) :
    ∃ (j' : J) (A : j ⟶ j') (b : ∀ i, j₁ i ⟶ j'), ∀ i, a i ≫ b i = A := by
  classical
  have := Fintype.ofFinite ι
  let O : Finset J := insert j (Finset.univ.image j₁)
  have hj : j ∈ O := Finset.mem_insert_self _ _
  have hj₁ (i : ι) : j₁ i ∈ O :=
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  let H : Finset (Σ' (X Y : J) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y) :=
    Finset.univ.image fun i ↦ ⟨j, j₁ i, hj, hj₁ i, a i⟩
  exact ⟨IsFiltered.sup O H, IsFiltered.toSup O H hj, fun i ↦ IsFiltered.toSup O H (hj₁ i),
    fun i ↦ IsFiltered.toSup_commutes O H hj (hj₁ i)
      (Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩

omit [SmallCategory J] in
/-- A finite family of objects of a filtered category has a cocone. -/
private lemma exists_cocone_of_finite' [Category J] [IsFiltered J] {ι : Type*} [Finite ι]
    (j₁ : ι → J) : ∃ j : J, Nonempty (∀ i, j₁ i ⟶ j) := by
  classical
  have := Fintype.ofFinite ι
  let O : Finset J := Finset.univ.image j₁
  exact ⟨IsFiltered.sup O ∅, ⟨fun i ↦ IsFiltered.toSup O ∅
    (Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩⟩

omit [SmallCategory J] in
/-- On a noetherian space, every covering sieve of an open `U` contains a finite covering
family of `U`. -/
lemma exists_finite_cover_of_mem [NoetherianSpace X] {U : Opens X} {R : Sieve U}
    (hR : R ∈ Opens.grothendieckTopology X U) :
    ∃ (ι : Type u) (_ : Finite ι) (V : ι → Opens X) (f : ∀ i, V i ⟶ U),
      (∀ i, R (f i)) ∧ U ≤ iSup V := by
  have hU : IsCompact (U : Set X) := NoetherianSpace.isCompact _
  choose V f hRf hx using fun x : U ↦ hR x.1 x.2
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun x : U ↦ (V x : Set X)) (fun x ↦ (V x).isOpen)
    fun y hy ↦ Set.mem_iUnion.2 ⟨⟨y, hy⟩, hx _⟩
  refine ⟨t, inferInstance, fun i ↦ V i.1, fun i ↦ f i.1, fun i ↦ hRf i.1, fun y hy ↦ ?_⟩
  obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.1 (ht hy)
  exact Opens.mem_iSup.2 ⟨⟨i, hi⟩, hyi⟩

variable [NoetherianSpace X] [IsFiltered J]

/-- **Sections of a filtered colimit are separated at a finite stage** on a noetherian space:
two sections of `D j` over `U` with the same image in `c.pt` agree in some later `D j'`. -/
theorem exists_map_eq_of_isColimit (hc : IsColimit c) {U : Opens X} {j : J}
    (t t' : (D.obj j).obj.obj (op U))
    (h : (c.ι.app j).hom.app (op U) t = (c.ι.app j).hom.app (op U) t') :
    ∃ (j' : J) (a : j ⟶ j'), (D.map a).hom.app (op U) t = (D.map a).hom.app (op U) t' := by
  obtain ⟨R, hR, hloc⟩ := exists_mem_forall_exists_map_eq hc t t' h
  obtain ⟨ι, _, V, f, hRf, hcov⟩ := exists_finite_cover_of_mem hR
  choose j₁ a₁ ha₁ using fun i ↦ hloc (f i) (hRf i)
  obtain ⟨j', A, b, hb⟩ := exists_comp_eq_of_finite' a₁
  refine ⟨j', A, (D.obj j').eq_of_locally_eq' V U f hcov _ _ fun i ↦ ?_⟩
  have hnat (z : (D.obj j).obj.obj (op U)) :
      (D.obj j').obj.map (f i).op ((D.map A).hom.app _ z) =
        (D.map (b i)).hom.app _ ((D.map (a₁ i)).hom.app _ ((D.obj j).obj.map (f i).op z)) := by
    rw [← hb i, D.map_comp]
    exact (NatTrans.naturality_apply (D.map (a₁ i) ≫ D.map (b i)).hom (f i).op z).symm
  rw [hnat, hnat, ha₁ i]

/-- **Sections of a filtered colimit come from a finite stage** on a noetherian space: every
section of `c.pt` over `U` is the image of a section of some `D j`. -/
theorem exists_app_eq_of_isColimit (hc : IsColimit c) {U : Opens X}
    (s : c.pt.obj.obj (op U)) :
    ∃ (j : J) (t : (D.obj j).obj.obj (op U)), (c.ι.app j).hom.app (op U) t = s := by
  obtain ⟨R, hR, hloc⟩ := exists_mem_forall_exists_app_eq hc s
  obtain ⟨ι, _, V, f, hRf, hcov⟩ := exists_finite_cover_of_mem hR
  choose j₁ t₁ ht₁ using fun i ↦ hloc (f i) (hRf i)
  obtain ⟨j, ⟨b⟩⟩ := exists_cocone_of_finite' j₁
  let t₂ (i : ι) : (D.obj j).obj.obj (op (V i)) := (D.map (b i)).hom.app _ (t₁ i)
  have ht₂ (i : ι) : (c.ι.app j).hom.app _ (t₂ i) = c.pt.obj.map (f i).op s := by
    rw [← ht₁ i, ← c.w (b i)]
    rfl
  have hpair (i₁ i₂ : ι) : ∃ (j' : J) (a : j ⟶ j'),
      (D.map a).hom.app _ ((D.obj j).obj.map (Opens.infLELeft (V i₁) (V i₂)).op (t₂ i₁)) =
        (D.map a).hom.app _ ((D.obj j).obj.map (Opens.infLERight (V i₁) (V i₂)).op
          (t₂ i₂)) := by
    refine exists_map_eq_of_isColimit hc _ _ ?_
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, ht₂, ht₂]
    change c.pt.obj.map _ (c.pt.obj.map _ s) = c.pt.obj.map _ (c.pt.obj.map _ s)
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp]
    rfl
  choose j₂ a₂ ha₂ using hpair
  obtain ⟨j', A, b', hb'⟩ := exists_comp_eq_of_finite' (fun p : ι × ι ↦ a₂ p.1 p.2)
  have hb'' (i₁ i₂ : ι) : a₂ i₁ i₂ ≫ b' (i₁, i₂) = A := hb' (i₁, i₂)
  let z (i : ι) : (D.obj j').obj.obj (op (V i)) := (D.map A).hom.app _ (t₂ i)
  have hz (i : ι) : (c.ι.app j').hom.app _ (z i) = c.pt.obj.map (f i).op s := by
    rw [← ht₂ i, ← c.w A]
    rfl
  have hA : Presheaf.IsCompatible (D.obj j').obj V z := fun i₁ i₂ ↦ by
    have e (k : ι) (r : V i₁ ⊓ V i₂ ⟶ V k) :
        (D.obj j').obj.map r.op (z k) =
          (D.map (b' (i₁, i₂))).hom.app _
            ((D.map (a₂ i₁ i₂)).hom.app _ ((D.obj j).obj.map r.op (t₂ k))) := by
      change (D.obj j').obj.map r.op ((D.map A).hom.app _ (t₂ k)) = _
      rw [← hb'' i₁ i₂, D.map_comp]
      exact (NatTrans.naturality_apply (D.map (a₂ i₁ i₂) ≫ D.map (b' (i₁, i₂))).hom r.op
        (t₂ k)).symm
    rw [e, e, ha₂ i₁ i₂]
  obtain ⟨y, hy, -⟩ := (D.obj j').existsUnique_gluing' V U f hcov z hA
  refine ⟨j', y, c.pt.eq_of_locally_eq' V U f hcov _ _ fun i ↦ ?_⟩
  rw [← hz i, ← hy i]
  exact (NatTrans.naturality_apply (c.ι.app j').hom (f i).op y).symm

/-- **Sections over an open of a noetherian space commute with filtered colimits**: the image of
a colimit cocone of a filtered diagram of abelian sheaves under the sections functor over `U` is
a colimit cocone. -/
noncomputable def isColimitSheafSectionsMapCocone (hc : IsColimit c) (U : Opens X) :
    IsColimit (((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (op U)).mapCocone c) := by
  have : ReflectsColimit
      (D ⋙ (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op U))
      (CategoryTheory.forget AddCommGrpCat.{u}) := reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (CategoryTheory.forget AddCommGrpCat.{u}) ?_
  refine Types.FilteredColimit.isColimitOf' _ _ (fun s ↦ ?_) (fun k t t' h ↦ ?_)
  · obtain ⟨k, t, ht⟩ := exists_app_eq_of_isColimit hc s
    exact ⟨k, t, ht.symm⟩
  · exact exists_map_eq_of_isColimit hc t t' h

/-- A filtered colimit of flasque sheaves on a noetherian space is flasque. -/
theorem isFlasque_of_isColimit (hc : IsColimit c) (hD : ∀ j, Presheaf.IsFlasque (D.obj j).obj) :
    Presheaf.IsFlasque c.pt.obj where
  epi {U V} i := by
    refine (AddCommGrpCat.epi_iff_surjective _).2 fun s ↦ ?_
    obtain ⟨j, t, rfl⟩ := exists_app_eq_of_isColimit hc s
    have := (hD j).epi i
    obtain ⟨t', rfl⟩ := (AddCommGrpCat.epi_iff_surjective _).1 this t
    exact ⟨(c.ι.app j).hom.app U t', (NatTrans.naturality_apply (c.ι.app j).hom i t').symm⟩

end Sections

section Cohomology

variable {X : TopCat.{u}} [NoetherianSpace X] {J : Type u} [SmallCategory J] [IsFiltered J]

/-- The functorial embedding of a diagram of abelian sheaves into the diagram of their
Godement sheaves. -/
noncomputable def toGodementDiagram (D : J ⥤ TopCat.Sheaf AddCommGrpCat.{u} X) :
    D ⟶ D ⋙ godementFunctor where
  app j := toGodementFunctor.app (D.obj j)
  naturality _ _ f := toGodementFunctor.naturality (D.map f)

/-- The statement that `Hⁿ` commutes with the colimit of the filtered diagram `D`, elementwise:
every class of `Hⁿ(colim D)` comes from some `Hⁿ(D j)`, and a class of `Hⁿ(D j)` vanishing in
`Hⁿ(colim D)` vanishes in some `Hⁿ(D j')`. -/
def HColimitProp (n : ℕ) (D : J ⥤ TopCat.Sheaf AddCommGrpCat.{u} X) : Prop :=
  (∀ x : Sheaf.H (colimit D) n, ∃ (j : J) (y : Sheaf.H (D.obj j) n),
      Sheaf.H.map (colimit.ι D j) n y = x) ∧
    ∀ (j : J) (y : Sheaf.H (D.obj j) n), Sheaf.H.map (colimit.ι D j) n y = 0 →
      ∃ (j' : J) (a : j ⟶ j'), Sheaf.H.map (D.map a) n y = 0

lemma hColimitProp_zero (D : J ⥤ TopCat.Sheaf AddCommGrpCat.{u} X) : HColimitProp 0 D := by
  refine ⟨fun x ↦ ?_, fun j y hy ↦ ?_⟩
  · obtain ⟨j, t, ht⟩ := exists_app_eq_of_isColimit (colimit.isColimit D)
      (Sheaf.H.equiv₀ _ isTerminalTop x)
    refine ⟨j, (Sheaf.H.equiv₀ _ isTerminalTop).symm t, ?_⟩
    rw [Sheaf.H.equiv₀_symm_naturality]
    apply (Sheaf.H.equiv₀ (colimit D) isTerminalTop).injective
    rw [AddEquiv.apply_symm_apply]
    exact ht
  · have h1 : (colimit.ι D j).hom.app (op ⊤) (Sheaf.H.equiv₀ _ isTerminalTop y) =
        (colimit.ι D j).hom.app (op ⊤) 0 := by
      rw [Sheaf.H.equiv₀_naturality, hy, map_zero, map_zero]
    obtain ⟨j', a, ha⟩ := exists_map_eq_of_isColimit (colimit.isColimit D) _ _ h1
    refine ⟨j', a, (Sheaf.H.equiv₀ _ isTerminalTop).injective ?_⟩
    rw [← Sheaf.H.equiv₀_naturality, map_zero, ha, map_zero]

/-- The dimension shifting step: if `Hⁿ` commutes with all filtered colimits, so does `Hⁿ⁺¹`,
on the first term of a short exact sequence of diagrams whose middle term is pointwise flasque.
-/
lemma hColimitProp_succ (n : ℕ) (ih : ∀ D : J ⥤ TopCat.Sheaf AddCommGrpCat.{u} X,
      HColimitProp n D)
    (S : ShortComplex (J ⥤ TopCat.Sheaf AddCommGrpCat.{u} X)) (hS : S.ShortExact)
    (hT : ∀ j, Presheaf.IsFlasque (S.X₂.obj j).obj) : HColimitProp (n + 1) S.X₁ := by
  -- Share the categorical structures used by all the cohomology maps in the diagram chase.
  let : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} := inferInstance
  let : Abelian (TopCat.Sheaf AddCommGrpCat.{u} X) := inferInstance
  let : HasExt.{u} (TopCat.Sheaf AddCommGrpCat.{u} X) := inferInstance
  let : HasColimitsOfShape J (TopCat.Sheaf AddCommGrpCat.{u} X) := inferInstance
  have hSj (j : J) : (S.map ((evaluation J _).obj j)).ShortExact := hS.map_of_exact _
  have hSc : (S.map colim).ShortExact := hS.map_of_exact _
  let φ (j : J) : S.map ((evaluation J _).obj j) ⟶ S.map colim :=
    { τ₁ := colimit.ι S.X₁ j
      τ₂ := colimit.ι S.X₂ j
      τ₃ := colimit.ι S.X₃ j
      comm₁₂ := by
        simp only [ShortComplex.map_f, colim_map, ι_colimMap, evaluation_obj_map]
      comm₂₃ := by
        simp only [ShortComplex.map_g, colim_map, ι_colimMap, evaluation_obj_map] }
  have hTj (j : J) : Subsingleton (Sheaf.H (S.map ((evaluation J _).obj j)).X₂ (n + 1)) :=
    IsFlasque.subsingleton_H n (S.X₂.obj j)
  have hTc : Subsingleton (Sheaf.H (S.map colim).X₂ (n + 1)) := by
    have : Presheaf.IsFlasque (colimit S.X₂).obj :=
      isFlasque_of_isColimit (colimit.isColimit S.X₂) hT
    exact IsFlasque.subsingleton_H n (colimit S.X₂)
  refine ⟨fun x ↦ ?_, fun j y hy ↦ ?_⟩
  · obtain ⟨y, rfl⟩ := Sheaf.H.δSucc_surjective hSc n x
    obtain ⟨j, y', rfl⟩ := (ih S.X₃).1 y
    exact ⟨j, Sheaf.H.δSucc (hSj j) n y', Sheaf.H.map_δSucc (hSj j) hSc (φ j) n y'⟩
  · have := hTj j
    obtain ⟨z, rfl⟩ : ∃ z : Sheaf.H (S.X₃.obj j) n, Sheaf.H.δSucc (hSj j) n z = y :=
      Sheaf.H.δSucc_surjective (hSj j) n y
    have h1 : Sheaf.H.δSucc hSc n (Sheaf.H.map (colimit.ι S.X₃ j) n z) = 0 :=
      (Sheaf.H.map_δSucc (hSj j) hSc (φ j) n z).symm.trans hy
    obtain ⟨w, hw⟩ := (Sheaf.H.exact_map_δSucc hSc n _).1 h1
    obtain ⟨k, wk, rfl⟩ := (ih S.X₂).1 w
    obtain ⟨m, fj, fk, -⟩ : ∃ (m : J) (_ : j ⟶ m) (_ : k ⟶ m), True :=
      ⟨_, IsFiltered.leftToMax j k, IsFiltered.rightToMax j k, True.intro⟩
    have e3 : Sheaf.H.map (colimit.ι S.X₃ m) n (Sheaf.H.map (S.X₃.map fj) n z) =
        Sheaf.H.map (colimit.ι S.X₃ j) n z := by
      rw [← Sheaf.H.map_comp_apply, colimit.w S.X₃ fj]
    have hmor : S.X₂.map fk ≫ S.g.app m ≫ colimit.ι S.X₃ m =
        colimit.ι S.X₂ k ≫ (S.map colim).g := by
      have hk : colimit.ι S.X₂ k ≫ (S.map colim).g = S.g.app k ≫ colimit.ι S.X₃ k :=
        (φ k).comm₂₃
      rw [hk, reassoc_of% (S.g.naturality fk), colimit.w S.X₃ fk]
    have e4 : Sheaf.H.map (colimit.ι S.X₃ m) n
          (Sheaf.H.map (S.g.app m) n (Sheaf.H.map (S.X₂.map fk) n wk)) =
        Sheaf.H.map (colimit.ι S.X₃ j) n z := by
      calc _ = Sheaf.H.map (S.X₂.map fk ≫ S.g.app m ≫ colimit.ι S.X₃ m) n wk := by
            rw [Sheaf.H.map_comp_apply, Sheaf.H.map_comp_apply]
        _ = Sheaf.H.map (colimit.ι S.X₂ k ≫ (S.map colim).g) n wk :=
          congrArg (fun f ↦ Sheaf.H.map f n wk) hmor
        _ = _ := by rw [Sheaf.H.map_comp_apply]; exact hw
    have hz' : Sheaf.H.map (colimit.ι S.X₃ m) n (Sheaf.H.map (S.X₃.map fj) n z -
        Sheaf.H.map (S.g.app m) n (Sheaf.H.map (S.X₂.map fk) n wk)) = 0 := by
      rw [map_sub, e3, e4, sub_self]
    have h2 := (ih S.X₃).2 m (Sheaf.H.map (S.X₃.map fj) n z -
      Sheaf.H.map (S.g.app m) n (Sheaf.H.map (S.X₂.map fk) n wk))
    obtain ⟨m', a, ha⟩ := h2 hz'
    refine ⟨m', fj ≫ a, ?_⟩
    have e := Sheaf.H.map_δSucc (hSj j) (hSj m')
      (S.mapNatTrans ((evaluation J _).map (fj ≫ a))) n z
    refine e.trans ?_
    have ha' : Sheaf.H.map (S.X₃.map a) n (Sheaf.H.map (S.X₃.map fj) n z) =
        Sheaf.H.map (S.X₃.map a) n
          (Sheaf.H.map (S.g.app m) n (Sheaf.H.map (S.X₂.map fk) n wk)) := by
      rw [← sub_eq_zero, ← map_sub]
      exact ha
    have key : Sheaf.H.map (S.X₃.map (fj ≫ a)) n z =
        Sheaf.H.map (S.g.app m') n (Sheaf.H.map (S.X₂.map (fk ≫ a)) n wk) := by
      calc Sheaf.H.map (S.X₃.map (fj ≫ a)) n z
          = Sheaf.H.map (S.X₃.map a) n (Sheaf.H.map (S.X₃.map fj) n z) := by
            rw [Functor.map_comp, Sheaf.H.map_comp_apply]
        _ = Sheaf.H.map (S.X₃.map a) n
            (Sheaf.H.map (S.g.app m) n (Sheaf.H.map (S.X₂.map fk) n wk)) := ha'
        _ = Sheaf.H.map (S.X₂.map fk ≫ S.g.app m ≫ S.X₃.map a) n wk := by
            rw [Sheaf.H.map_comp_apply, Sheaf.H.map_comp_apply]
        _ = Sheaf.H.map (S.X₂.map (fk ≫ a) ≫ S.g.app m') n wk := by
            rw [← S.g.naturality a, Functor.map_comp, Category.assoc]
        _ = _ := by rw [Sheaf.H.map_comp_apply]
    change Sheaf.H.δSucc (hSj m') n (Sheaf.H.map (S.X₃.map (fj ≫ a)) n z) = 0
    rw [key]
    exact (Sheaf.H.exact_map_δSucc (hSj m') n _).2 ⟨_, rfl⟩

/-- **Cohomology of a filtered colimit on a noetherian space**, elementwise: every class of
`Hⁿ(colim D)` comes from some `Hⁿ(D j)`, and a class of `Hⁿ(D j)` vanishing in `Hⁿ(colim D)`
vanishes in some `Hⁿ(D j')`. -/
theorem hColimitProp (n : ℕ) (D : J ⥤ TopCat.Sheaf AddCommGrpCat.{u} X) : HColimitProp n D := by
  induction n generalizing D with
  | zero => exact hColimitProp_zero D
  | succ n ih =>
    have : ∀ j, Mono ((toGodementDiagram D).app j) :=
      fun j ↦ (inferInstance : Mono (toGodementFunctor.app (D.obj j)))
    have : Mono (toGodementDiagram D) := NatTrans.mono_of_mono_app _
    exact hColimitProp_succ n ih
      (ShortComplex.mk (toGodementDiagram D) (cokernel.π _) (cokernel.condition _))
      (ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance)
      fun j ↦ (inferInstance : Presheaf.IsFlasque (godementFunctor.obj (D.obj j)).obj)

/-- Blueprint `lemma-uniform-bounds-pro-etale-affines`: Filtered colimits on a Noetherian Zariski
site.

On a noetherian topological space `X` (for instance the underlying space of a noetherian
scheme), sheaf cohomology commutes with filtered colimits of abelian sheaves:
`colimᵢ Hⁿ(X, Fᵢ) ≅ Hⁿ(X, colimᵢ Fᵢ)` for every `n`. -/
theorem preservesColimitsOfShape_functorH (J : Type u) [SmallCategory J] [IsFiltered J]
    (n : ℕ) :
    PreservesColimitsOfShape J (Sheaf.functorH.{u} (Opens.grothendieckTopology X) n) := by
  constructor
  intro D
  refine preservesColimit_of_preserves_colimit_cocone (colimit.isColimit D) ?_
  have : ReflectsColimit (D ⋙ Sheaf.functorH.{u} (Opens.grothendieckTopology X) n)
      (CategoryTheory.forget AddCommGrpCat.{u}) := reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (CategoryTheory.forget AddCommGrpCat.{u}) ?_
  refine Types.FilteredColimit.isColimitOf' _ _ (fun x ↦ ?_) (fun j y y' h ↦ ?_)
  · obtain ⟨j, y, hy⟩ := (hColimitProp n D).1 x
    exact ⟨j, y, hy.symm⟩
  · let y₁ : CategoryTheory.Sheaf.H (D.obj j) n := y
    let y₂ : CategoryTheory.Sheaf.H (D.obj j) n := y'
    have h' : CategoryTheory.Sheaf.H.map (colimit.ι D j) n y₁ =
        CategoryTheory.Sheaf.H.map (colimit.ι D j) n y₂ := h
    obtain ⟨j', a, ha⟩ := (hColimitProp n D).2 j (y₁ - y₂) (by rw [map_sub, h', sub_self])
    refine ⟨j', a, ?_⟩
    change CategoryTheory.Sheaf.H.map (D.map a) n y₁ = CategoryTheory.Sheaf.H.map (D.map a) n y₂
    rwa [map_sub, sub_eq_zero] at ha

end Cohomology

end TopCat.Sheaf
