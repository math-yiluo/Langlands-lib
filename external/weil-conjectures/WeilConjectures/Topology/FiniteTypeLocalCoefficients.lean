/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono

/-!
# Local coefficients for finite type module sheaves

Source: Stacks Project, Modules, Definition 01B5 and proof of Lemma 01B8;
Modules, Section 01AF and Lemma 01AG.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

private theorem bicone_section_decomposition
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : CategoryTheory.Sheaf J RingCat.{u}) {I : Type u} [Fintype I]
    (b : Bicone (fun _ : I ↦ SheafOfModules.unit R)) (hb : b.IsBilimit)
    (W : Cᵒᵖ) (z : b.pt.val.obj W) :
    z = ∑ j, (b.ι j).val.app W ((b.π j).val.app W z) := by
  let E := SheafOfModules.evaluation R W
  have : E.Additive := inferInstanceAs
    (SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj W).Additive
  have ht := IsBilimit.total hb
  have hh : (∑ j, E.map (b.π j ≫ b.ι j)) = 𝟙 (E.obj b.pt) :=
    (E.map_sum (fun j ↦ b.π j ≫ b.ι j) Finset.univ).symm.trans
      ((congrArg E.map ht).trans (E.map_id _))
  have hh' := congrArg (fun k ↦ k.hom z) hh
  dsimp [E, SheafOfModules.evaluation, SheafOfModules.forget,
    PresheafOfModules.evaluation] at hh'
  have hh'' : (∑ j, ((b.π j ≫ b.ι j).val.app W).hom z) = z := by
    simpa only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_id,
      LinearMap.id_apply, SheafOfModules.comp_val] using hh'
  simpa only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_id,
    LinearMap.id_apply, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
    E, SheafOfModules.evaluation, Functor.comp_map, SheafOfModules.forget_map,
    PresheafOfModules.evaluation_map, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.Hom.hom, Functor.comp_obj,
    SheafOfModules.forget_obj, PresheafOfModules.evaluation_obj]
    using hh''.symm

private theorem generator_map_apply
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : CategoryTheory.Sheaf J RingCat.{u})
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (M : SheafOfModules.{u} R) (σ : M.GeneratingSections)
    (W : Cᵒᵖ) (j : σ.I) (a : R.obj.obj W) :
    σ.π.val.app W ((SheafOfModules.ιFree j).val.app W a) =
      a • (show M.val.obj W from (σ.s j).val W) := by
  let f : SheafOfModules.unit R ⟶ M := SheafOfModules.ιFree j ≫ σ.π
  have hs : M.unitHomEquiv f = σ.s j :=
    congrFun (M.freeHomEquiv.apply_symm_apply σ.s) j
  have hs' : f.val.app W (1 : R.obj.obj W) = (σ.s j).val W :=
    congrArg (fun s : M.sections ↦ s.val W) hs
  have hlin := (f.val.app W).hom.map_smul a (1 : R.obj.obj W)
  have hlin' : f.val.app W a = a • (show M.val.obj W from (σ.s j).val W) := by
    simpa only [smul_eq_mul, mul_one, ModuleCat.Hom.hom, hs'] using hlin
  simpa only [f, SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] using hlin'

-- The restricted-site free sheaf and its biproduct require additional elaboration steps.
set_option backward.isDefEq.respectTransparency false in
/-- Finite type gives finitely many sections near a point such that every section is locally
an explicit linear combination of their restrictions.

Source: Stacks Project, Modules, Definition 01B5, proof of Lemma 01B8, and Section 01AF,
Lemma 01AG. (blueprint: lem-weil-pbc-finite-type-local-coefficients)

Proof: Choose finite local generators data for F. Its covering contains an open U around x;
evaluate the generating sections of F.over U at the terminal object of Over U, and identify
its finite index type with Fin n. The resulting map from the finite free sheaf to F.over U
is epi. For W contained in U, the local lifting criterion for epimorphisms gives a covering
of W on which t lifts to this free sheaf. A finite free sheaf has tuples of ring sections
as sections, since finite coproducts are finite products in modules. Evaluating the generating
map sends a tuple to the sum of its coordinates times the restricted generators. This gives
the coefficients at each point y of W. With n = 0 the free sheaf is zero, the sum is empty,
and local lifting gives zero restrictions of t. The empty open W has no points to check. -/
theorem exists_finite_type_local_coefficients (X : RingedSpace.{u})
    (F : SheafOfModules.{u} (moduleRings X)) (x : X) [F.IsFiniteType] :
    ∃ (U : Opens X), x ∈ U ∧ ∃ (n : ℕ) (s : Fin n → F.val.obj (op U)),
      ∀ (W : Opens X) (hW : W ≤ U) (t : F.val.obj (op W)) (y : X), y ∈ W →
        ∃ (V : Opens X) (hV : V ≤ W), y ∈ V ∧
          ∃ a : Fin n → (moduleRings X).obj.obj (op V),
            F.val.map (homOfLE hV).op t =
              ∑ j, a j • F.val.map (homOfLE (hV.trans hW)).op (s j) := by
  classical
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData F
  have hcover := (Opens.coversTop_iff X q.X).mp q.coversTop
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ i, q.X i by rw [hcover]; trivial)
  let U := q.X i
  let M := F.over U
  let σ := q.generators i
  have : σ.IsFiniteType := hq.isFiniteType i
  let : Fintype σ.I := Fintype.ofFinite _
  let n := Fintype.card σ.I
  let e : σ.I ≃ Fin n := Fintype.equivFin _
  let T : Over U := Over.mk (𝟙 U)
  let s (j : Fin n) : F.val.obj (op U) := (σ.s (e.symm j)).val (op T)
  refine ⟨U, hxi, n, s, ?_⟩
  intro W hW t y hy
  let Z : Over U := Over.mk (homOfLE hW)
  let p := (SheafOfModules.toSheaf ((moduleRings X).over U)).map σ.π
  have : Epi p := inferInstance
  have : CategoryTheory.Sheaf.IsLocallySurjective p :=
    (CategoryTheory.Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat p).mpr inferInstance
  have hc := CategoryTheory.Presheaf.imageSieve_mem
    ((Opens.grothendieckTopology X).over U) p.hom (U := op Z) t
  rw [GrothendieckTopology.mem_over_iff] at hc
  obtain ⟨V, f, hf, hyV⟩ := hc y hy
  rw [Sieve.overEquiv_iff] at hf
  obtain ⟨z, hz⟩ := hf
  refine ⟨V, leOfHom f, hyV, ?_⟩
  let D : Over U := Over.mk (f ≫ Z.hom)
  change (SheafOfModules.free (R := (moduleRings X).over U) σ.I).val.obj (op D) at z
  let b := Bicone.ofColimitCocone
    (t := (SheafOfModules.freeCofan (R := (moduleRings X).over U) σ.I))
    (SheafOfModules.isColimitFreeCofan (R := (moduleRings X).over U) σ.I)
  let c (j : σ.I) : (moduleRings X).obj.obj (op V) :=
    (b.π j).val.app (op D) z
  refine ⟨fun j ↦ c (e.symm j), ?_⟩
  have ht : F.val.map (homOfLE (leOfHom f)).op t = σ.π.val.app (op D) z := hz.symm
  apply ht.trans
  have hz' : z = ∑ j, (b.ι j).val.app (op D) (c j) :=
    bicone_section_decomposition ((moduleRings X).over U) b
      (biconeIsBilimitOfColimitCoconeOfIsColimit
        (t := SheafOfModules.freeCofan (R := (moduleRings X).over U) σ.I)
        (SheafOfModules.isColimitFreeCofan σ.I)) (op D) z
  apply (congrArg (fun z ↦ σ.π.val.app (op D) z) hz').trans
  apply (map_sum (σ.π.val.app (op D)).hom _ Finset.univ).trans
  apply Eq.trans _ (e.symm.sum_comp
    (fun j ↦ c j • F.val.map (homOfLE ((leOfHom f).trans hW)).op
      ((σ.s j).val (op T)))).symm
  apply Finset.sum_congr rfl
  intro j hj
  change σ.π.val.app (op D) ((SheafOfModules.ιFree j).val.app (op D) (c j)) = _
  apply (generator_map_apply ((moduleRings X).over U) M σ (op D) j (c j)).trans
  have hres := PresheafOfModules.sections_property (σ.s j)
    (Over.homMk D.hom : D ⟶ T).op
  have hres' : F.val.map (homOfLE ((leOfHom f).trans hW)).op
      ((σ.s j).val (op T)) = (σ.s j).val (op D) := hres
  exact congrArg (fun v : F.val.obj (op V) ↦ c j • v) hres'.symm

end AlgebraicGeometry.RingedSpace
