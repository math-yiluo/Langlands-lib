/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.Topology.Sheaves.Stalks

/-!
# The Čech complex of a family of open subsets

Let `X` be a topological space, `U : ι → Opens X` a family of open subsets and `P` a
presheaf of abelian groups on `X`. The (ordered) Čech complex `Č(U, P)` has in degree `k` the
cochains `c = (c y)_y`, indexed by the tuples `y : Fin (k + 1) → ι`, with
`c y ∈ P(U (y 0) ⊓ ⋯ ⊓ U (y k))`; the differential is the alternating sum of the restrictions
`(d c) y = ∑ i, (-1) ^ i • c (y ∘ Fin.succAbove i)`.

We show that `Č(U, P)` is exact in positive degrees in two situations: when restricting to one
of the members `U j` of the family is bijective on the sections over all the finite
intersections (in particular when `U j` contains all the other members), and when `P` is the
underlying presheaf of an injective abelian sheaf.

## Implementation notes

Mathlib's `CategoryTheory.cechComplexFunctor` builds the Čech complex of a family of objects of
any category with finite products through formal coproducts; its cochains are elements of
categorical products, which makes elementwise computations cumbersome. Here the cochains are
dependent functions, and the complex is the alternating coface map complex of an explicit
cosimplicial abelian group `TopCat.Presheaf.cechCosimplicialObject`.

## Main definitions

- `TopCat.Presheaf.cechComplex`: the Čech complex `Č(U, P)`, as a functor of `P`.
- `TopCat.Presheaf.godement`: the presheaf of all (not necessarily continuous) sections of a
  family of abelian groups indexed by the points of `X`.

## Main statements

- `TopCat.Presheaf.exactAt_cechComplex_of_bijective`: `Č(U, P)` is exact in positive degrees if
  restricting to some `U j` is bijective on the sections over the finite intersections.
- `TopCat.Presheaf.exactAt_cechComplex_of_le`: `Č(U, P)` is exact in positive degrees if some
  member of the family contains all the others.
- `TopCat.Presheaf.exactAt_cechComplex_of_injective`: the Čech complex of an injective abelian
  sheaf is exact in positive degrees.
-/

@[expose] public section

universe u v

open CategoryTheory Limits TopologicalSpace Opposite

namespace TopCat.Presheaf

variable {X : TopCat.{u}} {ι : Type v} (U : ι → Opens X)

lemma iInf_le_iInf_comp {k m : ℕ} (y : Fin (m + 1) → ι) (θ : Fin (k + 1) → Fin (m + 1)) :
    ⨅ l, U (y l) ≤ ⨅ l, U ((y ∘ θ) l) :=
  le_iInf fun l ↦ iInf_le _ (θ l)

/-- Restriction maps of a presheaf on `Opens X` compose: the composite of two restrictions is
the restriction along the composite inclusion. -/
lemma map_homOfLE_map_homOfLE_apply (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) {V W Z : Opens X}
    (h₁ : V ≤ W) (h₂ : W ≤ Z) (x : P.obj (op Z)) :
    P.map (homOfLE h₁).op (P.map (homOfLE h₂).op x) = P.map (homOfLE (h₁.trans h₂)).op x := by
  rw [← ConcreteCategory.comp_apply, ← P.map_comp]
  rfl

/-- Restricting a section along an equality of open subsets does nothing. -/
lemma map_homOfLE_self_apply (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) {V : Opens X} (h : V ≤ V)
    (x : P.obj (op V)) : P.map (homOfLE h).op x = x := by
  exact ConcreteCategory.congr_hom (P.map_id (op V)) x

/-- The Čech cochains of degree `k` of the family `U` with values in `P`: the families of
sections `c y ∈ P(U (y 0) ⊓ ⋯ ⊓ U (y k))` indexed by the tuples `y : Fin (k + 1) → ι`. -/
abbrev CechCochain (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (k : ℕ) : Type (max u v) :=
  ∀ y : Fin (k + 1) → ι, P.obj (op (⨅ l, U (y l)))

/-- The Čech cosimplicial abelian group of the family `U` with values in a presheaf `P`, as a
functor of `P`. In degree `k` it is the group `CechCochain U P k`, and a map `θ` of the simplex
category acts by `c ↦ (y ↦ c (y ∘ θ))`, restricted to the smaller intersection. -/
@[simps]
noncomputable def cechCosimplicialObject :
    ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ CosimplicialObject AddCommGrpCat.{max u v} where
  obj P :=
    { obj k := AddCommGrpCat.of (CechCochain U P k.len)
      map {k m} θ := AddCommGrpCat.ofHom (AddMonoidHom.pi fun y ↦
        (P.map (homOfLE (iInf_le_iInf_comp U y θ.toOrderHom)).op).hom.comp
          (Pi.evalAddMonoidHom _ (y ∘ θ.toOrderHom)))
      map_id k := by
        refine AddCommGrpCat.ext fun c ↦ funext fun y ↦ ?_
        exact map_homOfLE_self_apply P _ (c y)
      map_comp θ θ' := by
        refine AddCommGrpCat.ext fun c ↦ funext fun y ↦ ?_
        exact (map_homOfLE_map_homOfLE_apply P _ _ _).symm }
  map φ :=
    { app k := AddCommGrpCat.ofHom (AddMonoidHom.pi fun y ↦
        (φ.app _).hom.comp (Pi.evalAddMonoidHom _ y))
      naturality k m θ := by
        refine AddCommGrpCat.ext fun c ↦ funext fun y ↦ ?_
        exact NatTrans.naturality_apply φ (homOfLE _).op (c _) }
  map_id P := rfl
  map_comp φ ψ := rfl

/-- The Čech complex `Č(U, P)` of the family `U` with values in a presheaf `P`, as a functor
of `P`: the alternating coface map complex of `cechCosimplicialObject U`. -/
noncomputable def cechComplex :
    ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ CochainComplex AddCommGrpCat.{max u v} ℕ :=
  cechCosimplicialObject U ⋙ AlgebraicTopology.alternatingCofaceMapComplex _

instance : (cechComplex U).Additive where
  map_add := rfl

variable (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})

/-- The Čech differential is the alternating sum of the restrictions of the faces. -/
lemma cechComplex_d_apply (k : ℕ) (c : CechCochain U P k) (y : Fin (k + 2) → ι) :
    ((cechComplex U).obj P).d k (k + 1) c y =
      ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
        P.map (homOfLE (iInf_le_iInf_comp U y i.succAbove)).op (c (y ∘ i.succAbove)) := by
  have h : ((cechComplex U).obj P).d k (k + 1) =
      ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • ((cechCosimplicialObject U).obj P).δ i :=
    CochainComplex.of_d (fun m ↦ ((cechCosimplicialObject U).obj P).obj (SimplexCategory.mk m))
      (AlgebraicTopology.AlternatingCofaceMapComplex.objD _) k
  rw [h]
  refine (congrFun (AddCommGrpCat.sum_apply (fun i : Fin (k + 2) ↦
    (-1 : ℤ) ^ (i : ℕ) • ((cechCosimplicialObject U).obj P).δ i) Finset.univ c) y).trans ?_
  refine (Finset.sum_apply _ _ _).trans ?_
  rfl

@[simp]
lemma cechComplex_map_f_apply {P Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ Q) (k : ℕ)
    (c : CechCochain U P k) (y : Fin (k + 1) → ι) :
    ((cechComplex U).map φ).f k c y = φ.app _ (c y) :=
  rfl

/-- Exactness of the Čech complex in degree `q + 1`, in terms of cochains: every cocycle is a
coboundary. -/
lemma exactAt_cechComplex_iff (q : ℕ) :
    ((cechComplex U).obj P).ExactAt (q + 1) ↔
      ∀ c : CechCochain U P (q + 1), ((cechComplex U).obj P).d (q + 1) (q + 2) c = 0 →
        ∃ b : CechCochain U P q, ((cechComplex U).obj P).d q (q + 1) b = c := by
  rw [HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff]
  rfl

/-- Restrictions of the components of a cochain along two equal tuples agree. -/
lemma map_homOfLE_apply_congr {k : ℕ} (c : CechCochain U P k) {y y' : Fin (k + 1) → ι}
    (hy : y = y') {V : Opens X} (h : V ≤ ⨅ l, U (y l)) (h' : V ≤ ⨅ l, U (y' l)) :
    P.map (homOfLE h).op (c y) = P.map (homOfLE h').op (c y') := by
  subst hy
  rfl

/-- An open subset of `U j` and of `⨅ l, U (z l)` is contained in the intersection indexed by
the tuple `Fin.cons j z`. -/
lemma le_iInf_cons {k : ℕ} {V : Opens X} {j : ι} {z : Fin (k + 1) → ι} (hj : V ≤ U j)
    (hz : V ≤ ⨅ l, U (z l)) : V ≤ ⨅ l, U ((Fin.cons j z : Fin (k + 2) → ι) l) := by
  refine le_iInf fun l ↦ ?_
  cases l using Fin.cases with
  | zero => simpa using hj
  | succ l => simpa using hz.trans (iInf_le _ l)

/-- Deleting the entry `i + 1` of `Fin.cons j y` is the same as deleting the entry `i` of `y`. -/
lemma cons_comp_succAbove_succ {k : ℕ} (j : ι) (y : Fin (k + 1) → ι) (i : Fin (k + 1)) :
    (Fin.cons j y : Fin (k + 2) → ι) ∘ i.succ.succAbove =
      (Fin.cons j (y ∘ i.succAbove) : Fin (k + 1) → ι) := by
  funext l
  cases l using Fin.cases <;> simp

/-- The cocycle condition at the tuple `Fin.cons j y`, restricted to an open subset `V` of
`U j ⊓ ⨅ l, U (y l)`: the component `c y` is the alternating sum of the components
`c (Fin.cons j (y ∘ Fin.succAbove i))`. -/
lemma map_cocycle_eq_sum_cons {q : ℕ} (c : CechCochain U P (q + 1))
    (hc : ((cechComplex U).obj P).d (q + 1) (q + 2) c = 0) (j : ι)
    (y : Fin (q + 2) → ι) {V : Opens X} (hVj : V ≤ U j) (hV : V ≤ ⨅ l, U (y l)) :
    P.map (homOfLE hV).op (c y) = ∑ i : Fin (q + 2), (-1 : ℤ) ^ (i : ℕ) •
      P.map (homOfLE (le_iInf_cons U hVj (hV.trans (iInf_le_iInf_comp U y i.succAbove)))).op
        (c (Fin.cons j (y ∘ i.succAbove))) := by
  have hc' : ((cechComplex U).obj P).d (q + 1) (q + 1 + 1) c (Fin.cons j y) = 0 :=
    congrFun hc _
  have h₀ := congrArg (P.map (homOfLE (le_iInf_cons U hVj hV)).op)
    ((cechComplex_d_apply U P (q + 1) c (Fin.cons j y)).symm.trans hc')
  simp only [map_sum, map_zsmul, map_zero, map_homOfLE_map_homOfLE_apply] at h₀
  rw [Fin.sum_univ_succ, Fin.val_zero, pow_zero, one_smul,
    map_homOfLE_apply_congr U P c (by funext l; simp) _ hV] at h₀
  rw [eq_neg_of_add_eq_zero_left h₀, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Fin.val_succ, pow_succ, mul_neg_one, neg_smul, neg_neg,
    map_homOfLE_apply_congr U P c (cons_comp_succAbove_succ j y i)]

/-- If for some index `j` restricting to `U j` is bijective on the sections of `P` over all the
finite intersections of the family, then the Čech complex `Č(U, P)` is exact in positive
degrees: inserting the index `j` in the first slot, `(h c) y = c (Fin.cons j y)`, is a
contraction. -/
theorem exactAt_cechComplex_of_bijective {j : ι}
    (hj : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      Function.Bijective (P.map (homOfLE (inf_le_left : (⨅ l, U (y l)) ⊓ U j ≤ _)).op))
    (q : ℕ) : ((cechComplex U).obj P).ExactAt (q + 1) := by
  rw [exactAt_cechComplex_iff]
  intro c hc
  let e (z : Fin (q + 1) → ι) := Equiv.ofBijective _ (hj q z)
  have he (z : Fin (q + 1) → ι) (x) :
      P.map (homOfLE (inf_le_left : (⨅ l, U (z l)) ⊓ U j ≤ _)).op ((e z).symm x) = x :=
    (e z).apply_symm_apply x
  refine ⟨fun z ↦ (e z).symm (P.map (homOfLE (le_iInf_cons U inf_le_right inf_le_left)).op
    (c (Fin.cons j z))), funext fun (y : Fin (q + 2) → ι) ↦ (hj (q + 1) y).injective ?_⟩
  rw [map_cocycle_eq_sum_cons U P c hc j y inf_le_right inf_le_left, cechComplex_d_apply,
    map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_zsmul, map_homOfLE_map_homOfLE_apply, ← map_homOfLE_map_homOfLE_apply P
    (inf_le_inf_right (U j) (iInf_le_iInf_comp U y i.succAbove)) inf_le_left,
    he (y ∘ i.succAbove), map_homOfLE_map_homOfLE_apply]

/-- If some member `U j` of the family contains all the others, then the Čech complex
`Č(U, P)` is exact in positive degrees. -/
theorem exactAt_cechComplex_of_le {j : ι} (hj : ∀ i, U i ≤ U j) (q : ℕ) :
    ((cechComplex U).obj P).ExactAt (q + 1) := by
  refine exactAt_cechComplex_of_bijective U P (j := j) (fun k y ↦ ?_) q
  have heq : (⨅ l, U (y l)) ⊓ U j = ⨅ l, U (y l) := inf_eq_left.2 ((iInf_le _ 0).trans (hj _))
  rw [Subsingleton.elim (homOfLE _) (eqToHom heq), eqToHom_op, eqToHom_map]
  exact ConcreteCategory.bijective_of_isIso _

/-- The presheaf of all, not necessarily continuous, sections of a family `S` of abelian groups
indexed by the points of `X`: its sections over `W` are the families `(s x)_{x ∈ W}`. -/
@[simps]
noncomputable def godement (S : X → Type u) [∀ x, AddCommGroup (S x)] :
    (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj W := AddCommGrpCat.of (∀ x : W.unop, S x)
  map {W W'} f := AddCommGrpCat.ofHom (AddMonoidHom.pi fun x : W'.unop ↦
    Pi.evalAddMonoidHom (fun x : W.unop ↦ S x) ⟨x.1, f.unop.le x.2⟩)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The Čech complex of the presheaf of all sections of a family of abelian groups is exact in
positive degrees. -/
theorem exactAt_cechComplex_godement (S : X → Type u) [∀ x, AddCommGroup (S x)] (q : ℕ) :
    ((cechComplex U).obj (godement S)).ExactAt (q + 1) := by
  rw [exactAt_cechComplex_iff]
  intro c hc
  let j (x : X) (h : ∃ i, x ∈ U i) : ι := h.choose
  have hj (x : X) (h : ∃ i, x ∈ U i) : x ∈ U (j x h) := h.choose_spec
  have hmem {k : ℕ} (y : Fin (k + 1) → ι) (x : ↥(⨅ l, U (y l))) : x.1 ∈ U (y 0) :=
    (iInf_le _ 0 : _ ≤ U (y 0)) x.2
  refine ⟨fun y x ↦ c (Fin.cons (j x ⟨y 0, hmem y x⟩) y)
    ⟨x, le_iInf_cons U inf_le_right inf_le_left (Opens.mem_inf.2 ⟨x.2, hj _ _⟩)⟩, ?_⟩
  refine funext fun (y : Fin (q + 2) → ι) ↦ funext fun x ↦ ?_
  have h := congrFun (map_cocycle_eq_sum_cons U _ c hc (j x.1 ⟨y 0, hmem y x⟩) y
    (V := (⨅ l, U (y l)) ⊓ U (j x.1 ⟨y 0, hmem y x⟩)) inf_le_right inf_le_left)
    ⟨x.1, Opens.mem_inf.2 ⟨x.2, hj _ _⟩⟩
  refine (congrFun (cechComplex_d_apply U _ q _ y) x).trans ?_
  exact (Finset.sum_apply (M := fun x : ↥(⨅ l, U (y l)) ↦ S x) _ _ _).trans
    (h.trans (Finset.sum_apply (M := fun z : ↥((⨅ l, U (y l)) ⊓ U (j x.1 ⟨y 0, hmem y x⟩)) ↦
      S z) _ _ _)).symm

/-- The map from an abelian sheaf to the presheaf of all sections of its stalks, sending a
section to its germs. -/
noncomputable def toGodement
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    F.obj ⟶ godement fun x : X ↦
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.obj x : Type u) where
  app W := AddCommGrpCat.ofHom (AddMonoidHom.pi fun x : W.unop ↦
    (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) F.obj W.unop x.1 x.2).hom)
  naturality W W' f := by
    refine AddCommGrpCat.ext fun s ↦ funext fun x ↦ ?_
    exact TopCat.Presheaf.germ_res_apply F.obj f.unop x.1 x.2 s

instance (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    Mono (toGodement F) := by
  have (W : (Opens X)ᵒᵖ) : Mono ((toGodement F).app W) :=
    (AddCommGrpCat.mono_iff_injective _).2 fun s t hst ↦
      TopCat.Presheaf.section_ext F W.unop s t fun x hx ↦ congrFun hst ⟨x, hx⟩
  exact NatTrans.mono_of_mono_app _

/-- The Čech complex of an injective abelian sheaf is exact in positive degrees: the sheaf is a
direct summand of the presheaf of all sections of its stalks, whose Čech complex is exact. -/
theorem exactAt_cechComplex_of_injective
    (I : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) [Injective I]
    (q : ℕ) : ((cechComplex U).obj I.obj).ExactAt (q + 1) := by
  have hI : Injective I.obj := (sheafificationAdjunction _ _).map_injective I inferInstance
  have hr := Injective.comp_factorThru (𝟙 I.obj) (toGodement I)
  set ι := (cechComplex U).map (toGodement I)
  set ρ := (cechComplex U).map (Injective.factorThru (𝟙 I.obj) (toGodement I))
  have hιρ (k : ℕ) (c : ((cechComplex U).obj I.obj).X k) : ρ.f k (ι.f k c) = c := by
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, ← Functor.map_comp, hr,
      CategoryTheory.Functor.map_id, HomologicalComplex.id_f, ConcreteCategory.id_apply]
  rw [exactAt_cechComplex_iff]
  intro c hc
  obtain ⟨b, hb⟩ := (exactAt_cechComplex_iff U _ q).1 (exactAt_cechComplex_godement U _ q)
    (ι.f (q + 1) c) (by
      exact (ConcreteCategory.congr_hom (ι.comm (q + 1) (q + 2)) c).trans
        ((congrArg (ι.f (q + 2)) hc).trans (map_zero _)))
  exact ⟨ρ.f q b, (ConcreteCategory.congr_hom (ρ.comm q (q + 1)) b).trans
    ((congrArg (ρ.f (q + 1)) hb).trans (hιρ _ c))⟩

/-- Restriction of Čech cochains from a family `U` to a pointwise smaller family `U'`. -/
noncomputable def cechCochainRestrict (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
    {U U' : ι → Opens X} (h : ∀ i, U' i ≤ U i) (k : ℕ) :
    CechCochain U P k →+ CechCochain U' P k where
  toFun c y := P.map (homOfLE (iInf_mono fun l ↦ h (y l))).op (c y)
  map_zero' := funext fun _ ↦ map_zero _
  map_add' _ _ := funext fun _ ↦ map_add _ _ _

@[simp]
lemma cechCochainRestrict_apply (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
    {U U' : ι → Opens X} (h : ∀ i, U' i ≤ U i) (k : ℕ) (c : CechCochain U P k)
    (y : Fin (k + 1) → ι) :
    cechCochainRestrict P h k c y = P.map (homOfLE (iInf_mono fun l ↦ h (y l))).op (c y) :=
  rfl

/-- Restriction of Čech cochains to a pointwise smaller family commutes with the differential. -/
lemma cechComplex_d_cechCochainRestrict (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
    {U U' : ι → Opens X} (h : ∀ i, U' i ≤ U i) (k : ℕ) (c : CechCochain U P k) :
    ((cechComplex U').obj P).d k (k + 1) (cechCochainRestrict P h k c) =
      cechCochainRestrict P h (k + 1) (((cechComplex U).obj P).d k (k + 1) c) := by
  funext (y : Fin (k + 1 + 1) → ι)
  dsimp only [cechCochainRestrict, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  simp only [cechComplex_d_apply, map_sum, map_zsmul,
    ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

end TopCat.Presheaf
