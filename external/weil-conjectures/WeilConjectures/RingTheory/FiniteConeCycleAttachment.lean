/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Category.ModuleCat.Free
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.LinearAlgebra.Basis.Prod

/-!
# Attaching supplied finite free cone cycles

Source: Stacks Project, Tag 064U, descending induction step.
(blueprint: lem-pc-ring-finite-cone-cycle-attachment).
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

private theorem epi_homologyMap_of_two_isIso
    {R : Type u} [CommRing R] {K L : CochainComplex (ModuleCat.{v} R) ℤ}
    (φ : K ⟶ L) (i : ℤ) [IsIso (φ.f i)] [IsIso (φ.f (i + 1))] :
    Epi (HomologicalComplex.homologyMap φ i) := by
  let S := (HomologicalComplex.shortComplexFunctor (ModuleCat.{v} R)
    (ComplexShape.up ℤ) i).map φ
  have h2 : IsIso S.τ₂ := by change IsIso (φ.f i); infer_instance
  have h3 : Mono S.τ₃ := by
    change Mono (φ.f ((ComplexShape.up ℤ).next i))
    rw [(ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl)]
    infer_instance
  have : IsIso (HomologicalComplex.cyclesMap φ i) :=
    ShortComplex.isIso_cyclesMap_of_isIso_of_mono' S h2 h3
  exact ShortComplex.epi_homologyMap_of_epi_cyclesMap' S inferInstance

/-- Attach a given finite free family of cone cycles that generates its cohomology.

Source: Stacks Project, Tag 064U, proof of (2) implies (1), induction step.
(blueprint: lem-pc-ring-finite-cone-cycle-attachment).

Proof: Put D = mappingCone f. Compose q with the cycle inclusion into D^(n-1)
and project to F^n and C^(n-1), obtaining a and c. The cycle condition gives
 d_F a = 0 and f a + d_C c = 0. Define G to have P in degree n-1, F^i in
all degrees i >= n, and zero below n-1. Its new differential is a and its
other differentials are those of F. Define g by -c in degree n-1 and f in
the retained degrees. The two cycle equations prove the complex and chain-map
identities. Define j by the identities in degrees at least n and the unique
maps from the zero terms of F below n. Thus j composed with g equals f and
j is invertible in each retained degree. The new term lies below or at b
because n <= b+1; P and the retained terms are finite free, as are zero terms.
In degrees at least n-1, the new cone has the same terms and outgoing maps as
D. Its boundaries in degree n-1 are the old boundaries plus the image of
q in cycles (up to a harmless sign); boundaries in higher degrees do not change.
Consequently its degree-(n-1) homology is the cokernel of q followed by the
homology projection, which is zero by hq, and its higher homology is that of D.
Transfer these homology computations to Q using homologyFunctorFactors. Empty
families and the zero ring are included: an epimorphism from zero forces the
obstruction homology to be zero. No finiteness or choice of generators is
asserted here: the actual module P and cycle map q are inputs. -/
theorem exists_finiteFree_cone_cycle_attachment (R : Type u) [CommRing R] [Small.{v} R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (C F : CochainComplex (ModuleCat.{v} R) ℤ) (f : F ⟶ C) (b n : ℤ)
    (hn : n ≤ b + 1) (hlow : F.IsStrictlyGE n) (hupp : F.IsStrictlyLE b)
    (hfree : ∀ i : ℤ, Module.Free R (F.X i) ∧ Module.Finite R (F.X i))
    (hvan : ∀ i : ℤ, n ≤ i → IsZero
      ((homologyFunctor (ModuleCat.{v} R) i).obj (Q.obj (CochainComplex.mappingCone f))))
    (P : ModuleCat.{v} R) [Module.Free R P] [Module.Finite R P]
    (q : P ⟶ (CochainComplex.mappingCone f).cycles (n - 1))
    (hq : Epi (q ≫ (CochainComplex.mappingCone f).homologyπ (n - 1))) :
    ∃ (G : CochainComplex (ModuleCat.{v} R) ℤ) (g : G ⟶ C) (j : F ⟶ G),
      G.IsStrictlyGE (n - 1) ∧ G.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Free R (G.X i) ∧ Module.Finite R (G.X i)) ∧
      (∀ i : ℤ, n - 1 ≤ i → IsZero
        ((homologyFunctor (ModuleCat.{v} R) i).obj
          (Q.obj (CochainComplex.mappingCone g)))) ∧
      j ≫ g = f ∧ (∀ i : ℤ, n ≤ i → IsIso (j.f i)) := by
  classical
  let D := CochainComplex.mappingCone f
  let a : P ⟶ F.X n := q ≫ D.iCycles (n - 1) ≫
    (CochainComplex.mappingCone.fst f).1.v (n - 1) n (by omega)
  let c : P ⟶ C.X (n - 1) := q ≫ D.iCycles (n - 1) ≫
    (CochainComplex.mappingCone.snd f).v (n - 1) (n - 1) (by omega)
  have ha : a ≫ F.d n (n + 1) = 0 := by
    have h := congrArg (fun t ↦ q ≫ t ≫
      (CochainComplex.mappingCone.fst f).1.v n (n + 1) rfl)
      (D.iCycles_d (n - 1) n)
    dsimp [D] at h
    rw [Category.assoc, CochainComplex.mappingCone.d_fst_v f _ _ _ (by omega) rfl]
      at h
    simpa [a] using h
  have hc : a ≫ f.f n + c ≫ C.d (n - 1) n = 0 := by
    have h := congrArg (fun t ↦ q ≫ t ≫
      (CochainComplex.mappingCone.snd f).v n n (by omega))
      (D.iCycles_d (n - 1) n)
    dsimp [D] at h
    rw [Category.assoc, CochainComplex.mappingCone.d_snd_v f _ _ (by omega)] at h
    simpa [a, c, Preadditive.comp_add] using h
  let A := (CochainComplex.singleFunctor (ModuleCat.{v} R) n).obj P
  let k : A ⟶ F := CochainComplex.HomComplex.Cocycle.homOf
    (CochainComplex.HomComplex.Cocycle.fromSingleMk a (by omega : n + 0 = n)
      (n + 1) rfl ha)
  let α : CochainComplex.HomComplex.Cochain A C (-1) :=
    CochainComplex.HomComplex.Cochain.fromSingleMk (-c) (by omega : n + (-1) = n - 1)
  have heq : CochainComplex.HomComplex.δ (-1) 0 α =
      CochainComplex.HomComplex.Cochain.ofHom (k ≫ f) := by
    rw [CochainComplex.HomComplex.Cochain.δ_fromSingleMk (-c)
      (by omega : n + (-1) = n - 1) 0 n (by omega)]
    have hca : (-c) ≫ C.d (n - 1) n = a ≫ f.f n := by
      rw [Preadditive.neg_comp]
      exact neg_eq_of_add_eq_zero_left hc
    simp only [hca]
    simpa only [k, CochainComplex.HomComplex.Cocycle.fromSingleMk_coe,
      CochainComplex.HomComplex.Cochain.ofHom_comp,
      CochainComplex.HomComplex.Cocycle.cochain_ofHom_homOf_eq_coe] using
      (CochainComplex.HomComplex.Cochain.fromSingleMk_postcomp a
        (by omega : n + 0 = n) f)
  let G := CochainComplex.mappingCone k
  let g : G ⟶ C := CochainComplex.mappingCone.desc k α f heq
  let j : F ⟶ G := CochainComplex.mappingCone.inr k
  have hj : j ≫ g = f := CochainComplex.mappingCone.inr_desc k α f heq
  have hGlo : G.IsStrictlyGE (n - 1) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    refine ⟨?_, ?_⟩
    · exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) n P (i + 1)
        (by omega)
    · let _ := hlow
      exact F.isZero_of_isStrictlyGE n i (by omega)
  have hGup : G.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    refine ⟨?_, ?_⟩
    · exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) n P (i + 1)
        (by omega)
    · let _ := hupp
      exact F.isZero_of_isStrictlyLE b i hi
  have hGfree : ∀ i : ℤ, Module.Free R (G.X i) ∧ Module.Finite R (G.X i) := by
    intro i
    have : Module.Free R (F.X i) := (hfree i).1
    have : Module.Finite R (F.X i) := (hfree i).2
    have : Module.Free R (A.X (i + 1)) := by
      by_cases h : i + 1 = n
      · exact Module.Free.of_equiv (HomologicalComplex.singleObjXIsoOfEq
          (ComplexShape.up ℤ) n P (i + 1) h).symm.toLinearEquiv
      · have hz := HomologicalComplex.isZero_single_obj_X
          (ComplexShape.up ℤ) n P (i + 1) h
        have : Subsingleton (A.X (i + 1)) := ModuleCat.subsingleton_of_isZero hz
        infer_instance
    have : Module.Finite R (A.X (i + 1)) := by
      by_cases h : i + 1 = n
      · exact Module.Finite.equiv (HomologicalComplex.singleObjXIsoOfEq
          (ComplexShape.up ℤ) n P (i + 1) h).symm.toLinearEquiv
      · have hz := HomologicalComplex.isZero_single_obj_X
          (ComplexShape.up ℤ) n P (i + 1) h
        have : Subsingleton (A.X (i + 1)) := ModuleCat.subsingleton_of_isZero hz
        infer_instance
    let e : G.X i ≅ ModuleCat.of R (A.X (i + 1) × F.X i) :=
      HomologicalComplex.homotopyCofiber.XIsoBiprod k i (i + 1) rfl ≪≫
        ModuleCat.biprodIsoProd _ _
    exact ⟨Module.Free.of_equiv e.symm.toLinearEquiv,
      Module.Finite.equiv e.symm.toLinearEquiv⟩
  have hjiso : ∀ i : ℤ, n ≤ i → IsIso (j.f i) := by
    intro i hi
    let s : G.X i ⟶ F.X i := (CochainComplex.mappingCone.snd k).v i i (by omega)
    refine ⟨⟨s, ?_, ?_⟩⟩
    · exact CochainComplex.mappingCone.inr_f_snd_v k i
    · apply CochainComplex.mappingCone.ext_from k (i + 1) i rfl
      · have hz := HomologicalComplex.isZero_single_obj_X
          (ComplexShape.up ℤ) n P (i + 1) (by omega)
        exact hz.eq_of_src _ _
      · simp only [s, j, CochainComplex.mappingCone.inr_f_snd_v_assoc]
        exact (Category.comp_id _).symm
  have heqt : CochainComplex.HomComplex.δ 0 1 (CochainComplex.mappingCone.snd f) +
      ((CochainComplex.mappingCone.fst f).postcomp j).1.comp
        (CochainComplex.HomComplex.Cochain.ofHom g) (by omega) = 0 := by
    simp only [CochainComplex.mappingCone.δ_snd, CochainComplex.HomComplex.Cocycle.postcomp_coe,
      CochainComplex.HomComplex.Cochain.comp_assoc_of_third_is_zero_cochain,
      ← CochainComplex.HomComplex.Cochain.ofHom_comp, hj]
    exact neg_add_cancel _
  let t : D ⟶ CochainComplex.mappingCone g := CochainComplex.mappingCone.lift g
    ((CochainComplex.mappingCone.fst f).postcomp j)
    (CochainComplex.mappingCone.snd f) heqt
  have ht1 (i : ℤ) : t.f i ≫ (CochainComplex.mappingCone.fst g).1.v i (i + 1) rfl =
      (CochainComplex.mappingCone.fst f).1.v i (i + 1) rfl ≫ j.f (i + 1) := by
    simp [t, CochainComplex.HomComplex.Cocycle.postcomp]
  have ht2 (i : ℤ) : t.f i ≫ (CochainComplex.mappingCone.snd g).v i i (by omega) =
      (CochainComplex.mappingCone.snd f).v i i (by omega) := by
    simp [t]
  have htiso : ∀ i : ℤ, n - 1 ≤ i → IsIso (t.f i) := by
    intro i hi
    have : IsIso (j.f (i + 1)) := hjiso (i + 1) (by omega)
    let s : (CochainComplex.mappingCone g).X i ⟶ D.X i :=
      (CochainComplex.mappingCone.fst g).1.v i (i + 1) rfl ≫
        inv (j.f (i + 1)) ≫ (CochainComplex.mappingCone.inl f).v (i + 1) i (by omega) +
      (CochainComplex.mappingCone.snd g).v i i (by omega) ≫
        (CochainComplex.mappingCone.inr f).f i
    refine ⟨⟨s, ?_, ?_⟩⟩
    · apply CochainComplex.mappingCone.ext_to f i (i + 1) rfl
      · simp only [Int.reduceNeg, Preadditive.comp_add, reassoc_of% ht1 i,
          IsIso.hom_inv_id_assoc, Preadditive.add_comp, Category.assoc,
          CochainComplex.mappingCone.inl_v_fst_v, Category.comp_id,
          CochainComplex.mappingCone.inr_f_fst_v, comp_zero, add_zero, Category.id_comp, s]
      · simp only [Int.reduceNeg, Preadditive.comp_add, reassoc_of% ht2 i,
          Preadditive.add_comp, Category.assoc, CochainComplex.mappingCone.inl_v_snd_v,
          comp_zero, CochainComplex.mappingCone.inr_f_snd_v, Category.comp_id,
          zero_add, Category.id_comp, s]
    · apply CochainComplex.mappingCone.ext_to g i (i + 1) rfl
      · simp only [Int.reduceNeg, Preadditive.add_comp, Category.assoc, ht1,
          CochainComplex.mappingCone.inl_v_fst_v_assoc, IsIso.inv_hom_id,
          Category.comp_id, CochainComplex.mappingCone.inr_f_fst_v_assoc,
          zero_comp, comp_zero, add_zero, Category.id_comp, s]
      · simp only [Int.reduceNeg, Preadditive.add_comp, Category.assoc, ht2,
          CochainComplex.mappingCone.inl_v_snd_v, comp_zero,
          CochainComplex.mappingCone.inr_f_snd_v, Category.comp_id,
          zero_add, Category.id_comp, s]
  have hGvan : ∀ i : ℤ, n - 1 ≤ i → IsZero
      ((homologyFunctor (ModuleCat.{v} R) i).obj (Q.obj (CochainComplex.mappingCone g))) := by
    intro i hi
    let E := CochainComplex.mappingCone g
    have hE : IsZero (E.homology i) := by
      have : IsIso (t.f i) := htiso i hi
      have : IsIso (t.f (i + 1)) := htiso (i + 1) (by omega)
      have hr : Epi (HomologicalComplex.homologyMap t i) :=
        epi_homologyMap_of_two_isIso t i
      let _ := hr
      by_cases hi' : i = n - 1
      · subst i
        have hkill : q ≫ D.homologyπ (n - 1) ≫
            HomologicalComplex.homologyMap t (n - 1) = 0 := by
          let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n P
          let u : P ⟶ G.X (n - 1) := e.inv ≫
            (CochainComplex.mappingCone.inl k).v n (n - 1) (by omega)
          have hud : u ≫ G.d (n - 1) n = a ≫ j.f n := by
            dsimp only [u, G]
            rw [Category.assoc, CochainComplex.mappingCone.inl_v_d k n (n - 1)
              (n + 1) (by omega) (by omega)]
            simp [k, e, Category.assoc, j, A]
          have hug : u ≫ g.f (n - 1) = -c := by
            simp [u, g, α, e, Category.assoc]
          let x : P ⟶ E.X (n - 2) := (-u) ≫
            (CochainComplex.mappingCone.inl g).v (n - 1) (n - 2) (by omega)
          have hx : q ≫ D.iCycles (n - 1) ≫ t.f (n - 1) =
              x ≫ E.d (n - 2) (n - 1) := by
            apply CochainComplex.mappingCone.ext_to g (n - 1) n (by omega)
            · dsimp only [E]
              simp only [x, Category.assoc, CochainComplex.mappingCone.d_fst_v g
                (n - 2) (n - 1) n (by omega) (by omega), Preadditive.comp_neg,
                Preadditive.neg_comp, neg_neg]
              simp [t, CochainComplex.HomComplex.Cocycle.postcomp, a, hud, Category.assoc]
            · dsimp only [E]
              simp only [x, Category.assoc, CochainComplex.mappingCone.d_snd_v g
                (n - 2) (n - 1) (by omega), Preadditive.comp_add,
                CochainComplex.mappingCone.inl_v_fst_v_assoc,
                CochainComplex.mappingCone.inl_v_snd_v_assoc, zero_comp, add_zero,
                Preadditive.neg_comp, hug, neg_neg]
              simp [t, c]
          have hcycles : q ≫ HomologicalComplex.cyclesMap t (n - 1) =
              E.liftCycles (q ≫ D.iCycles (n - 1) ≫ t.f (n - 1)) n
                (by simp) (by rw [hx, Category.assoc, E.d_comp_d, comp_zero]) := by
            apply (cancel_mono (E.iCycles (n - 1))).1
            simp only [E, Category.assoc, HomologicalComplex.cyclesMap_i,
              HomologicalComplex.liftCycles_i]
          rw [HomologicalComplex.homologyπ_naturality, ← Category.assoc, hcycles]
          exact E.liftCycles_homologyπ_eq_zero_of_boundary _ n (by simp) x hx
        let _ := hq
        exact IsZero.of_epi_eq_zero (HomologicalComplex.homologyMap t (n - 1))
          (zero_of_epi_comp (q ≫ D.homologyπ (n - 1)) hkill)
      · have hn' : n ≤ i := by omega
        have hz : IsZero (D.homology i) :=
          IsZero.of_iso (hvan i hn')
            ((homologyFunctorFactors (ModuleCat.{v} R) i).app D).symm
        exact IsZero.of_epi (HomologicalComplex.homologyMap t i) hz
    exact IsZero.of_iso hE ((homologyFunctorFactors (ModuleCat.{v} R) i).app E)
  exact ⟨G, g, j, hGlo, hGup, hGfree, hGvan, hj, hjiso⟩

end DerivedCategory
