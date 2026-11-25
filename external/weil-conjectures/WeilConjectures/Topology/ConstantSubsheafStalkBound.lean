/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Sheaves.Abelian
public import WeilConjectures.Topology.AbelianOpenExtensionByZero
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.GroupTheory.Archimedean
import WeilConjectures.Topology.AbelianOpenExtensionByZeroStalks
public import Mathlib.CategoryTheory.Limits.IsConnected
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # A uniform bound for the integer stalk subgroups

Source: Stacks Project, Cohomology, Lemma 0A38, first paragraph
(blueprint: lem-sc-constant-subsheaf-stalk-bound).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

private theorem constantSubsheaf_canonical_stalks (X : TopCat.{u}) (A : AddCommGrpCat.{u}) :
    ∃ e : ∀ x : X,
      TopCat.Presheaf.stalk
        ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj A).obj x ≅ A,
      ∀ (x : X) (U : Opens X) (hx : x ∈ U),
        (toSheafify (Opens.grothendieckTopology X)
          ((Functor.const (Opens X)ᵒᵖ).obj A)).app (op U) ≫
        TopCat.Presheaf.germ
          ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj A).obj
          U x hx ≫ (e x).hom = 𝟙 A := by
  classical
  let P : TopCat.Presheaf AddCommGrpCat.{u} X := (Functor.const (Opens X)ᵒᵖ).obj A
  let sf (x : X) := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have hu (x : X) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} P
  let eP (x : X) : (sf x).obj P ≅ A := by
    letI : IsConnected (OpenNhds x) := isConnected_of_isTerminal _ isTerminalTop
    change colimit ((OpenNhds.inclusion x).op ⋙ P) ≅ A
    exact (colimit.isColimit _).coconePointUniqueUpToIso
      (isColimitConstCocone (OpenNhds x)ᵒᵖ A)
  let e (x : X) :=
    (asIso ((sf x).map (toSheafify (Opens.grothendieckTopology X) P))).symm.trans (eP x)
  refine ⟨e, ?_⟩
  intro x U hx
  change _ ≫ _ ≫ (e x).hom = _
  erw [← TopCat.Presheaf.stalkFunctor_map_germ_assoc]
  simp only [e, Iso.trans_hom, Iso.symm_hom, asIso_inv]
  simp only [sf, P] at *
  erw [IsIso.hom_inv_id_assoc]
  change colimit.ι _ _ ≫ (eP x).hom = _
  let : IsConnected (OpenNhds x) := isConnected_of_isTerminal _ isTerminalTop
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit ((Functor.const (OpenNhds x)ᵒᵖ).obj A))
    (isColimitConstCocone (OpenNhds x)ᵒᵖ A) (op ⟨U, hx⟩)

private theorem constantSubsheaf_section_locallyConstant (X : TopCat.{u}) (A : AddCommGrpCat.{u})
    (e : ∀ x : X,
      TopCat.Presheaf.stalk
        ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj A).obj x ≅ A)
    (he : ∀ (x : X) (U : Opens X) (hx : x ∈ U),
        (toSheafify (Opens.grothendieckTopology X)
          ((Functor.const (Opens X)ᵒᵖ).obj A)).app (op U) ≫
        TopCat.Presheaf.germ
          ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj A).obj
          U x hx ≫ (e x).hom = 𝟙 A)
    (U : Opens X)
    (t : ToType (((constantSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).obj A).obj.obj (op U))) :
    IsLocallyConstant (fun x : U ↦
      (e x.val).hom (TopCat.Presheaf.germ
        ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj A).obj
        U x.val x.property t)) := by
  classical
  let P : TopCat.Presheaf AddCommGrpCat.{u} X := (Functor.const (Opens X)ᵒᵖ).obj A
  let F := (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj A
  let η := toSheafify (Opens.grothendieckTopology X) P
  have hsurj : TopCat.Presheaf.IsLocallySurjective η := by
    apply (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks η).mpr
    intro x
    let := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} P
    exact (ConcreteCategory.bijective_of_isIso _).surjective
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  obtain ⟨V, hVU, ⟨a, ha⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff η).mp hsurj U t x.val x.property
  change η.app (op V) a = F.obj.map (homOfLE hVU).op t at ha
  refine ⟨{y : U | y.val ∈ V}, V.isOpen.preimage continuous_subtype_val, hxV, ?_⟩
  have hvalue (y : U) (hy : y.val ∈ V) :
      (e y.val).hom (TopCat.Presheaf.germ F.obj U y.val y.property t) = a := by
    have hger := TopCat.Presheaf.germ_res_apply F.obj (homOfLE hVU) y.val hy t
    have hc := congrArg (fun k ↦ (ConcreteCategory.hom k) a) (he y.val V hy)
    change (e y.val).hom (TopCat.Presheaf.germ F.obj V y.val hy
      (η.app (op V) a)) = a at hc
    erw [← hger, ← ha]
    exact hc
  intro y hy
  exact (hvalue y hy).trans (hvalue x hxV).symm

private theorem constantSubsheaf_range_integer_bound (M : AddCommGrpCat.{u})
    (h : M ⟶ AddCommGrpCat.of (ULift.{u} ℤ)) (b : ℕ)
    (hb : h ≠ 0 → ∃ t : M, h t ≠ 0 ∧ (h t).down.natAbs ≤ b) :
    ∃ a : ℕ, a ≤ b ∧ Set.range (fun t : M ↦ h t) =
      Set.range (fun z : ULift.{u} ℤ ↦ (a : ℤ) • z) := by
  classical
  let hZ : M →+ ℤ := AddEquiv.ulift.toAddMonoidHom.comp h.hom
  let H := hZ.range
  obtain ⟨k, hk⟩ := AddSubgroup.isAddCyclic H
  have hH : H = AddSubgroup.zmultiples ((k : ℤ).natAbs : ℤ) := by
    rw [Int.zmultiples_natAbs]
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := hk ⟨x, hx⟩
      exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n, by simpa using congrArg Subtype.val hn⟩
    · intro hx
      obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
      exact H.zsmul_mem k.2 n
  have hrange : Set.range (fun t : M ↦ h t) =
      Set.range (fun z : ULift.{u} ℤ ↦ ((k : ℤ).natAbs : ℤ) • z) := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      have ht : (h t).down ∈ H := ⟨t, rfl⟩
      rw [hH, Int.mem_zmultiples_iff] at ht
      obtain ⟨n, hn⟩ := ht
      refine ⟨ULift.up n, ?_⟩
      apply ULift.ext
      simpa [Int.zsmul_eq_mul, mul_comm] using hn.symm
    · rintro ⟨z, rfl⟩
      have hz : (((k : ℤ).natAbs : ℤ) • z).down ∈ AddSubgroup.zmultiples ((k : ℤ).natAbs : ℤ) := by
        rw [Int.mem_zmultiples_iff]
        exact ⟨z.down, by simp [mul_comm]⟩
      rw [← hH] at hz
      obtain ⟨t, ht⟩ := hz
      refine ⟨t, ?_⟩
      apply ULift.ext
      exact ht
  refine ⟨(k : ℤ).natAbs, ?_, hrange⟩
  by_cases hz : h = 0
  · have hmem : ULift.up ((k : ℤ).natAbs : ℤ) ∈ Set.range (fun t : M ↦ h t) := by
      rw [hrange]
      exact ⟨ULift.up 1, by apply ULift.ext; simp⟩
    obtain ⟨t, ht⟩ := hmem
    rw [hz] at ht
    have : (k : ℤ).natAbs = 0 := by
      have := congrArg ULift.down ht
      simpa using this.symm
    simp [this]
  · obtain ⟨t, ht, htb⟩ := hb hz
    have hd : ((k : ℤ).natAbs : ℤ) ∣ (h t).down := by
      rw [← Int.mem_zmultiples_iff, ← hH]
      exact ⟨t, rfl⟩
    have hpos : 0 < (h t).down.natAbs := by
      apply Int.natAbs_pos.mpr
      intro he
      apply ht
      apply ULift.ext
      exact he
    exact (Nat.le_of_dvd hpos (by simpa using Int.natAbs_dvd_natAbs.mpr hd)).trans htb

private theorem constantSubsheaf_integer_hom_zero {D : AddCommGrpCat.{u}}
    (f : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ D) (hf : f (ULift.up 1) = 0) : f = 0 := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro z
  have hz : z = z.down • (ULift.up 1 : ULift.{u} ℤ) := by
    apply ULift.ext
    simp
  change f.hom z = 0
  rw [hz, map_zsmul, hf, zsmul_zero]

set_option backward.isDefEq.respectTransparency false in
/-- Finite generation on compact opens bounds the positive generators of all stalk images.
The chosen isomorphisms `e` identify the ambient constant-sheaf stalks with the integers;
`a = 0` includes the zero subgroup and the empty generating family.

Source: Stacks Project, Cohomology, Lemma 0A38, first paragraph.
Proof: construct canonical integer stalk coordinates using preservation of stalks by
sheafification and the colimit of a constant diagram of open neighborhoods. Local
surjectivity of the sheafification unit shows that each constant-sheaf section gives a
locally constant function in these coordinates. On a compact generating open, this
function has finite range. Bound the absolute integer values for each generating section
and sum these finitely many bounds to obtain b. At a point, stalks preserve the generating
epimorphism and coproduct. A nonzero stalk image therefore has a nonzero component from
one generating summand. Extension-by-zero stalks make that component zero outside its
open and identify it inside with a homomorphism from the integers. Such a homomorphism
is determined by the image of 1, the coordinate of our section germ, bounded by b.
Finally every integer subgroup is generated by an integer k. Its nonnegative generator
is |k|, which divides the nonzero bounded section value, hence is at most b. The zero
subgroup has generator zero. This proves the same bound as normalization by clopen
fibres, without constructing the normalized finite family.
(blueprint: lem-sc-constant-subsheaf-stalk-bound). -/
theorem constantSubsheaf_stalk_bound
    (X : TopCat.{u})
    (K C : Sheaf AddCommGrpCat X)
    (ι : K ⟶ C)
    [Mono ι]
    (hC : Nonempty (C ≅
      (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))))
    (hgen : ∃ (n : ℕ) (U : Fin n → Opens X)
      (_ : ∀ i, IsCompact ((U i : Opens X) : Set X)),
      ∃ g : (∐ fun i => (abelianOpenExtensionByZero (U i)).obj
        ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (U i)))
          AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ⟶ K, Epi g) :
    ∃ e : ∀ x : X, TopCat.Presheaf.stalk C.obj x ≅ AddCommGrpCat.of (ULift.{u} ℤ),
      ∃ b : ℕ, ∀ x : X, ∃ a : ℕ, a ≤ b ∧
      Set.range (fun t : ToType (TopCat.Presheaf.stalk K.obj x) ↦
        (e x).hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ι.hom t)) =
      Set.range (fun z : ULift.{u} ℤ ↦ (a : ℤ) • z) := by
  classical
  obtain ⟨isoC⟩ := hC
  let Z := AddCommGrpCat.of (ULift.{u} ℤ)
  let F := (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj Z
  obtain ⟨eZ, heZ⟩ := constantSubsheaf_canonical_stalks X Z
  let e (x : X) :=
    ((Sheaf.forget AddCommGrpCat.{u} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso isoC).trans (eZ x)
  obtain ⟨n, U, hU, g, hg⟩ := hgen
  let := hg
  let G (i : Fin n) :=
    (constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (U i)))
      AddCommGrpCat.{u}).obj Z
  let E (i : Fin n) := (abelianOpenExtensionByZero (U i)).obj (G i)
  let δ (i : Fin n) : E i ⟶ F := Sigma.ι E i ≫ g ≫ ι ≫ isoC.hom
  let η (i : Fin n) := toSheafify
    (Opens.grothendieckTopology ((Opens.toTopCat X).obj (U i)))
    ((Functor.const (Opens ((Opens.toTopCat X).obj (U i)))ᵒᵖ).obj Z)
  let s (i : Fin n) : ToType (F.obj.obj (op (U i))) :=
    (η i).app (op ((Opens.map (U i).inclusion').obj (U i))) ≫
      abelianOpenExtensionSection (U i) (G i) (U i) le_rfl ≫
      (δ i).hom.app (op (U i)) |>.hom <| ULift.up 1
  let values (i : Fin n) : LocallyConstant (U i) (ULift.{u} ℤ) :=
    ⟨fun x ↦ (eZ x.val).hom (TopCat.Presheaf.germ F.obj (U i) x.val x.property (s i)),
      constantSubsheaf_section_locallyConstant X Z eZ heZ (U i) (s i)⟩
  have hbnd (i : Fin n) : ∃ b : ℕ, ∀ x : U i, (values i x).down.natAbs ≤ b := by
    let : CompactSpace (U i) := isCompact_iff_compactSpace.mp (hU i)
    let T := (values i).range_finite.toFinset
    refine ⟨T.sup (fun z ↦ z.down.natAbs), ?_⟩
    intro x
    exact Finset.le_sup (f := fun z ↦ z.down.natAbs)
      ((values i).range_finite.mem_toFinset.mpr ⟨x, rfl⟩)
  choose B hB using hbnd
  let b := ∑ i : Fin n, B i
  have hvb (i : Fin n) (x : U i) : (values i x).down.natAbs ≤ b :=
    (hB i x).trans (Finset.single_le_sum (fun j _ ↦ Nat.zero_le (B j)) (Finset.mem_univ i))
  refine ⟨e, b, ?_⟩
  intro x
  let sf := Sheaf.forget AddCommGrpCat.{u} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  let j := sf.map (ι ≫ isoC.hom) ≫ (eZ x).hom
  obtain ⟨a, hab, ha⟩ := constantSubsheaf_range_integer_bound (sf.obj K) j b (by
    intro hj
    have hcomp : sf.map g ≫ j ≠ 0 := by
      intro hzero
      apply hj
      apply (cancel_epi (sf.map g)).mp
      simpa using hzero
    have hi : ∃ i : Fin n, sf.map (Sigma.ι E i) ≫ sf.map g ≫ j ≠ 0 := by
      by_contra hi
      have hzero : ∀ i : Fin n, sf.map (Sigma.ι E i) ≫ sf.map g ≫ j = 0 := by
        simpa using hi
      apply hcomp
      apply (isColimitOfHasCoproductOfPreservesColimit sf E).hom_ext
      intro i
      simpa using hzero i.as
    obtain ⟨i, hi⟩ := hi
    by_cases hx : x ∈ U i
    · let xi : U i := ⟨x, hx⟩
      obtain ⟨eG, heG⟩ := constantSubsheaf_canonical_stalks ((Opens.toTopCat X).obj (U i)) Z
      obtain ⟨eE, heE, _, _, _⟩ := abelianOpenExtensionByZero_stalks X (U i)
      let q : Z ≅ sf.obj (E i) := (eG xi).symm.trans (eE xi (G i))
      have hunit : (eG xi).inv = (η i).app
          (op ((Opens.map (U i).inclusion').obj (U i))) ≫
        TopCat.Presheaf.germ (G i).obj ((Opens.map (U i).inclusion').obj (U i)) xi hx := by
        apply (cancel_mono (eG xi).hom).mp
        simp only [Iso.inv_hom_id]
        exact (heG xi ((Opens.map (U i).inclusion').obj (U i)) hx).symm
      have hq : q.hom ≫ sf.map (δ i) ≫ (eZ x).hom =
          (η i).app (op ((Opens.map (U i).inclusion').obj (U i))) ≫
          abelianOpenExtensionSection (U i) (G i) (U i) le_rfl ≫
          (δ i).hom.app (op (U i)) ≫ TopCat.Presheaf.germ F.obj (U i) x hx ≫
          (eZ x).hom := by
        dsimp only [q, Iso.trans_hom, Iso.symm_hom]
        rw [hunit]
        have hEE := congrArg (fun k ↦ k ≫ sf.map (δ i) ≫ (eZ x).hom)
          (heE xi (G i) (U i) le_rfl hx)
        have hEE' :
            TopCat.Presheaf.germ (G i).obj ((Opens.map (U i).inclusion').obj (U i))
              xi hx ≫ (eE xi (G i)).hom ≫ sf.map (δ i) ≫ (eZ x).hom =
            abelianOpenExtensionSection (U i) (G i) (U i) le_rfl ≫
              TopCat.Presheaf.germ (E i).obj (U i) x hx ≫ sf.map (δ i) ≫
              (eZ x).hom := by
          simpa only [Category.assoc] using hEE
        change (η i).app (op ((Opens.map (U i).inclusion').obj (U i))) ≫
          (TopCat.Presheaf.germ (G i).obj ((Opens.map (U i).inclusion').obj (U i))
            xi hx ≫ (eE xi (G i)).hom ≫ sf.map (δ i) ≫ (eZ x).hom) = _
        rw [hEE']
        dsimp only [sf, Functor.comp_map]
        erw [TopCat.Presheaf.stalkFunctor_map_germ_assoc]
        rfl
      let c := sf.map (Sigma.ι E i) ≫ sf.map g ≫ j
      have hqval : (q.hom ≫ c) (ULift.up 1) = values i xi := by
        have hh := congrArg (fun k ↦ (ConcreteCategory.hom k) (ULift.up 1)) hq
        simpa [c, δ, j, s, values, Functor.map_comp, ConcreteCategory.comp_apply,
          Category.assoc] using hh
      have hn : values i xi ≠ 0 := by
        intro hv
        have hc : q.hom ≫ c = 0 := constantSubsheaf_integer_hom_zero _ (hqval.trans hv)
        apply hi
        apply (cancel_epi q.hom).mp
        simpa using hc
      refine ⟨(sf.map (Sigma.ι E i) ≫ sf.map g) (q.hom (ULift.up 1)), ?_, ?_⟩
      · change (q.hom ≫ c) (ULift.up 1) ≠ 0
        rwa [hqval]
      · change ((q.hom ≫ c) (ULift.up 1)).down.natAbs ≤ b
        rw [hqval]
        exact hvb i xi
    · obtain ⟨_, _, _, hz, _⟩ := abelianOpenExtensionByZero_stalks X (U i)
      exact (hi ((hz (G i) x hx).eq_of_src _ _)).elim)
  refine ⟨a, hab, ?_⟩
  have hjmap : sf.map ι ≫ (e x).hom = j := by
    change sf.map ι ≫ sf.map isoC.hom ≫ (eZ x).hom =
      sf.map (ι ≫ isoC.hom) ≫ (eZ x).hom
    rw [Functor.map_comp, Category.assoc]
  change Set.range (fun t : sf.obj K ↦ (sf.map ι ≫ (e x).hom) t) =
    Set.range (fun z : ULift.{u} ℤ ↦ (a : ℤ) • z)
  rw [hjmap]
  exact ha


end TopCat.Sheaf
