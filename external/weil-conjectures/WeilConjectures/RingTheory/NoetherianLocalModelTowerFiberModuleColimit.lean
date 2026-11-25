/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NoetherianLocalModelTowerFiberRingColimit
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Module.TransferInstance

/-! # The module colimit of the explicit closed-fibre system

Source: Stacks Project, Algebra, Tag 00R7, proof by Noetherian approximation.
(blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-module-colimit)

The image union of stage ideal-times-module submodules constructs the limit
submodule. Stage representatives and eventual equality prove the quotient group
cocone colimiting. Tensor-quotient equivalences construct its additive comparison.
The top quotient tensor action is transported across these proved equivalences;
formulas on representatives prove semilinearity and compatibility with fiberPsi.
-/

@[expose] public section

universe z u v w t

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Module.NoetherianLocalModelTower

section Union

variable {I : Type z} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (A : I → Type u) [∀ i, CommRing (A i)]
  (N : I → Type t) [∀ i, AddCommGroup (N i)] [∀ i, Module (A i) (N i)]
  (g : ∀ i j, i ≤ j → A i →+* A j)
  (f : ∀ i j, i ≤ j → N i →+ N j)
  (L : Type v) [CommRing L] (P : Type w) [AddCommGroup P] [Module L P]
  (π : ∀ i, A i →+* L) (ν : ∀ i, N i →+ P)
  (hπ : ∀ i j h, (π j).comp (g i j h) = π i)
  (hν : ∀ i j h, (ν j).comp (f i j h) = ν i)
  (hrep : ∀ x : L, ∃ i a, π i a = x)
  (hsem : ∀ i a x, ν i (a • x) = π i a • ν i x)
  (J : ∀ i, Submodule (A i) (N i))
  (hJ : ∀ i j h x, x ∈ J i → f i j h x ∈ J j)

private def submoduleUnion : Submodule L P where
  carrier := {x | ∃ i a, a ∈ J i ∧ ν i a = x}
  zero_mem' := ⟨Classical.arbitrary I, 0, (J _).zero_mem, map_zero _⟩
  add_mem' := by
    rintro x y ⟨i, a, ha, rfl⟩ ⟨j, b, hb, rfl⟩
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    refine ⟨k, f i k hik a + f j k hjk b,
      (J k).add_mem (hJ i k hik a ha) (hJ j k hjk b hb), ?_⟩
    rw [map_add]
    exact congrArg₂ (· + ·) (DFunLike.congr_fun (hν i k hik) a)
      (DFunLike.congr_fun (hν j k hjk) b)
  smul_mem' := by
    rintro r x ⟨i, a, ha, rfl⟩
    obtain ⟨j, b, rfl⟩ := hrep r
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    refine ⟨k, g j k hjk b • f i k hik a,
      (J k).smul_mem _ (hJ i k hik a ha), ?_⟩
    rw [hsem]
    exact congrArg₂ (· • ·) (RingHom.congr_fun (hπ j k hjk) b)
      (DFunLike.congr_fun (hν i k hik) a)

end Union

variable {R : Type u} {S : Type v} {S' : Type w} {M : Type t}
  [CommRing R] [CommRing S] [CommRing S'] [IsLocalRing R] [AddCommGroup M]
  [Algebra R S] [Algebra S S'] [Module S' M] [Module S M]
  [IsScalarTower S S' M]
  (X : Module.NoetherianLocalModelTower R S S' M)

attribute [local instance] Module.NoetherianLocalModelTower.preorder
  Module.NoetherianLocalModelTower.nonempty Module.NoetherianLocalModelTower.directed
  Module.NoetherianLocalModelTower.commR Module.NoetherianLocalModelTower.commS
  Module.NoetherianLocalModelTower.commT Module.NoetherianLocalModelTower.localR
  Module.NoetherianLocalModelTower.algRS Module.NoetherianLocalModelTower.algST
  Module.NoetherianLocalModelTower.algRT Module.NoetherianLocalModelTower.towerRST
  Module.NoetherianLocalModelTower.algRLimit Module.NoetherianLocalModelTower.algSLimit
  Module.NoetherianLocalModelTower.algTLimit Module.NoetherianLocalModelTower.addN
  Module.NoetherianLocalModelTower.moduleT Module.NoetherianLocalModelTower.moduleS
  Module.NoetherianLocalModelTower.towerSTN

omit [IsLocalRing R] [IsScalarTower S S' M] in
/-- (blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-module-colimit) -/
theorem nmap_smulS (i j : X.ι) (h : i ≤ j) (a : X.S₀ i) (x : X.N₀ i) :
    X.nmap i j h (a • x) = X.smap i j h a • X.nmap i j h x := by
  rw [← algebraMap_smul (X.T₀ i) a x, X.nmap_smul]
  have he := RingHom.congr_fun (X.st_comm i j h) a
  change X.tmap i j h (algebraMap (X.S₀ i) (X.T₀ i) a) =
    algebraMap (X.S₀ j) (X.T₀ j) (X.smap i j h a) at he
  rw [he, algebraMap_smul]

omit [IsLocalRing R] in
/-- (blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-module-colimit) -/
theorem nlimit_smulS (i : X.ι) (a : X.S₀ i) (x : X.N₀ i) :
    X.nlimit i (a • x) = algebraMap (X.S₀ i) S a • X.nlimit i x := by
  rw [← algebraMap_smul (X.T₀ i) a x, X.nlimit_smul]
  have he := RingHom.congr_fun (X.st_limit_comm i) a
  change algebraMap (X.T₀ i) S' (algebraMap (X.S₀ i) (X.T₀ i) a) =
    algebraMap S S' (algebraMap (X.S₀ i) S a) at he
  rw [he, algebraMap_smul]

/-- (blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-module-colimit) -/
abbrev FiberSubmoduleS (i : X.ι) : Submodule (X.S₀ i) (X.N₀ i) :=
  X.fiberIdealS i • ⊤

/-- (blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-module-colimit) -/
abbrev FiberSubmoduleLimitS : Submodule S M :=
  Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) • ⊤

omit [IsLocalRing R] [IsScalarTower S S' M] in
/-- (blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-module-colimit) -/
theorem fiberSubmoduleS_transition (i j : X.ι) (h : i ≤ j) (x : X.N₀ i)
    (hx : x ∈ X.FiberSubmoduleS i) : X.nmap i j h x ∈ X.FiberSubmoduleS j := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha n hn
    rw [X.nmap_smulS]
    exact Submodule.smul_mem_smul (X.fiberIdealS_transition i j h ha) (Submodule.mem_top)
  · intro a b ha hb
    rw [map_add]
    exact Submodule.add_mem _ ha hb

/-- (blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-module-colimit) -/
theorem fiberSubmoduleS_limit (i : X.ι) (x : X.N₀ i)
    (hx : x ∈ X.FiberSubmoduleS i) : X.nlimit i x ∈
      FiberSubmoduleLimitS (R := R) (S := S) (M := M) := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha n hn
    rw [X.nlimit_smulS]
    exact Submodule.smul_mem_smul (X.fiberIdealS_limit i ha) (Submodule.mem_top)
  · intro a b ha hb
    rw [map_add]
    exact Submodule.add_mem _ ha hb

/-- (blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-module-colimit) -/
theorem fiberSubmoduleS_limit_rep (m : M)
    (hm : m ∈ FiberSubmoduleLimitS (R := R) (S := S) (M := M)) :
    ∃ i n, n ∈ X.FiberSubmoduleS i ∧ X.nlimit i n = m := by
  let J := submoduleUnion X.S₀ X.N₀ X.smap X.nmap S M
    (fun i ↦ algebraMap (X.S₀ i) S) X.nlimit X.slimit_comm X.nlimit_comm
    X.slimit_surj X.nlimit_smulS X.FiberSubmoduleS X.fiberSubmoduleS_transition
  have hJ : FiberSubmoduleLimitS (R := R) (S := S) (M := M) ≤ J := by
    apply Submodule.smul_le.mpr
    intro a ha n hn
    obtain ⟨i, b, hb, he⟩ := X.fiberIdealS_limit_rep a ha
    obtain ⟨j, x, hx⟩ := X.nlimit_surj n
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    refine ⟨k, X.smap i k hik b • X.nmap j k hjk x,
      Submodule.smul_mem_smul (X.fiberIdealS_transition i k hik hb) Submodule.mem_top, ?_⟩
    rw [X.nlimit_smulS]
    exact congrArg₂ (· • ·) ((RingHom.congr_fun (X.slimit_comm i k hik) b).trans he)
      ((DFunLike.congr_fun (X.nlimit_comm j k hjk) x).trans hx)
  exact hJ hm

/-- (blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-module-colimit) -/
theorem fiberN_eventual_zero (i : X.ι) (n : X.N₀ i)
    (hn : X.nlimit i n ∈ FiberSubmoduleLimitS (R := R) (S := S) (M := M)) :
    ∃ j h, X.nmap i j h n ∈ X.FiberSubmoduleS j := by
  obtain ⟨j, x, hx, he⟩ := X.fiberSubmoduleS_limit_rep _ hn
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  have hk : X.nlimit k (X.nmap i k hik n) = X.nlimit k (X.nmap j k hjk x) :=
    (DFunLike.congr_fun (X.nlimit_comm i k hik) n).trans
      (he.symm.trans (DFunLike.congr_fun (X.nlimit_comm j k hjk) x).symm)
  obtain ⟨l, hkl, hl⟩ := X.nlimit_eq k _ _ hk
  refine ⟨l, hik.trans hkl, ?_⟩
  have hmem := X.fiberSubmoduleS_transition k l hkl _
    (X.fiberSubmoduleS_transition j k hjk x hx)
  rw [← hl] at hmem
  simpa only [X.nSystem.map_map] using hmem

/-- (blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-module-colimit) -/
noncomputable def fiberDQuotEquiv (i : X.ι) :
    X.fiberD.obj i ≃+ X.N₀ i ⧸ X.FiberSubmoduleS i :=
  (X.fiberDEquiv i).trans
    (TensorProduct.quotTensorEquivQuotSMul (X.N₀ i) (X.fiberIdealS i)).toAddEquiv

omit [IsLocalRing R] [IsScalarTower S S' M] in
/-- (blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-module-colimit) -/
theorem fiberDQuotEquiv_tmul (i : X.ι) (a : X.T₀ i) (n : X.N₀ i) :
    X.fiberDQuotEquiv i (ULift.up (Ideal.Quotient.mk _ a ⊗ₜ[X.T₀ i] n)) =
      Submodule.Quotient.mk (a • n) := by
  simp [fiberDQuotEquiv, fiberDEquiv, fiberNEquiv]
  rfl

omit [IsLocalRing R] [IsScalarTower S S' M] in
/-- (blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-module-colimit) -/
theorem fiberDQuotEquiv_symm_mk (i : X.ι) (n : X.N₀ i) :
    (X.fiberDQuotEquiv i).symm (Submodule.Quotient.mk n) =
      ULift.up (1 ⊗ₜ[X.T₀ i] n) := by
  apply (X.fiberDQuotEquiv i).injective
  simpa using (X.fiberDQuotEquiv_tmul i 1 n).symm

/-- (blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-module-colimit) -/
def nlimitSLinear (i : X.ι) : X.N₀ i →ₛₗ[algebraMap (X.S₀ i) S] M where
  toAddHom := X.nlimit i
  map_smul' := X.nlimit_smulS i

/-- (blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-module-colimit) -/
noncomputable def fiberDLimit (i : X.ι) :
    X.fiberD.obj i →+ M ⧸ FiberSubmoduleLimitS (R := R) (S := S) (M := M) :=
  ((X.FiberSubmoduleS i).mapQ
    (FiberSubmoduleLimitS (R := R) (S := S) (M := M)) (X.nlimitSLinear i)
    (X.fiberSubmoduleS_limit i)).toAddMonoidHom.comp (X.fiberDQuotEquiv i).toAddMonoidHom

/-- (blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-module-colimit) -/
theorem fiberDLimit_tmul (i : X.ι) (a : X.T₀ i) (n : X.N₀ i) :
    X.fiberDLimit i (ULift.up (Ideal.Quotient.mk _ a ⊗ₜ[X.T₀ i] n)) =
      Submodule.Quotient.mk (X.nlimit i (a • n)) := by
  simp [fiberDLimit, X.fiberDQuotEquiv_tmul, nlimitSLinear]

/-- (blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-module-colimit) -/
theorem fiberDLimit_mk (i : X.ι) (n : X.N₀ i) :
    X.fiberDLimit i ((X.fiberDQuotEquiv i).symm (Submodule.Quotient.mk n)) =
      Submodule.Quotient.mk (X.nlimit i n) := by
  simp [fiberDLimit, nlimitSLinear]

omit [IsLocalRing R] [IsScalarTower S S' M] in
/-- (blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-module-colimit) -/
theorem fiberDQuotEquiv_map_mk (i j : X.ι) (h : i ≤ j) (n : X.N₀ i) :
    X.fiberDQuotEquiv j ((X.fiberD.map (homOfLE h)).hom
      ((X.fiberDQuotEquiv i).symm (Submodule.Quotient.mk n))) =
      Submodule.Quotient.mk (X.nmap i j h n) := by
  rw [X.fiberDQuotEquiv_symm_mk]
  change X.fiberDQuotEquiv j (ULift.up (X.fiberNMap i j h (1 ⊗ₜ n))) = _
  rw [X.fiberNMap_tmul, map_one]
  simpa using X.fiberDQuotEquiv_tmul j 1 (X.nmap i j h n)

/-- (blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-module-colimit) -/
theorem fiberDLimit_naturality (i j : X.ι) (f : i ⟶ j) :
    (X.fiberDLimit j).comp (X.fiberD.map f).hom = X.fiberDLimit i := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨q, rfl⟩ := (X.fiberDQuotEquiv i).symm.surjective x
  obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  simp only [AddMonoidHom.comp_apply]
  have h := X.fiberDQuotEquiv_map_mk i j (leOfHom f) n
  have he := congrArg (X.fiberDQuotEquiv j).symm h
  simp only [AddEquiv.symm_apply_apply] at he
  rw [he, X.fiberDLimit_mk, X.fiberDLimit_mk]
  exact congrArg Submodule.Quotient.mk (DFunLike.congr_fun
    (X.nlimit_comm i j (leOfHom f)) n)

/-- (blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-module-colimit) -/
noncomputable def fiberDCocone : Cocone X.fiberD where
  pt := AddCommGrpCat.of (ULift.{max u v w t}
    (M ⧸ FiberSubmoduleLimitS (R := R) (S := S) (M := M)))
  ι := {
    app := fun i ↦ AddCommGrpCat.ofHom
      (AddEquiv.ulift.symm.toAddMonoidHom.comp (X.fiberDLimit i))
    naturality := by
      intro i j f
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro x
      exact congrArg ULift.up (DFunLike.congr_fun (X.fiberDLimit_naturality i j f) x) }

/-- (blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-module-colimit) -/
noncomputable def fiberDCoconeIsColimit : IsColimit X.fiberDCocone := by
  let : PreservesColimit X.fiberD (forget AddCommGrpCat) :=
    preservesColimit_of_preserves_colimit_cocone
      (AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit.{max u v w, t} X.fiberD)
      (Types.TypeMax.colimitCoconeIsColimit.{max u v w, t}
        (X.fiberD ⋙ forget AddCommGrpCat))
  let := reflectsColimit_of_reflectsIsomorphisms X.fiberD (forget AddCommGrpCat)
  apply isColimitOfReflects (forget AddCommGrpCat)
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective _ x.down
    obtain ⟨i, n, hn⟩ := X.nlimit_surj m
    refine ⟨i, (X.fiberDQuotEquiv i).symm (Submodule.Quotient.mk n), ?_⟩
    change x = ULift.up (X.fiberDLimit i _)
    rw [X.fiberDLimit_mk, hn, hm]
    rfl
  · intro i x y h
    obtain ⟨qx, hx⟩ := (X.fiberDQuotEquiv i).symm.surjective x
    obtain ⟨qy, hy⟩ := (X.fiberDQuotEquiv i).symm.surjective y
    obtain ⟨nx, rfl⟩ := Submodule.Quotient.mk_surjective _ qx
    obtain ⟨ny, rfl⟩ := Submodule.Quotient.mk_surjective _ qy
    subst x y
    have he : Submodule.Quotient.mk (X.nlimit i nx) =
        (Submodule.Quotient.mk (X.nlimit i ny) :
          M ⧸ FiberSubmoduleLimitS (R := R) (S := S) (M := M)) := by
      have hh := congrArg ULift.down h
      change X.fiberDLimit i ((X.fiberDQuotEquiv i).symm (Submodule.Quotient.mk nx)) =
        X.fiberDLimit i ((X.fiberDQuotEquiv i).symm (Submodule.Quotient.mk ny)) at hh
      simpa only [X.fiberDLimit_mk] using hh
    have hz : X.nlimit i (nx - ny) ∈
        FiberSubmoduleLimitS (R := R) (S := S) (M := M) := by
      apply (Submodule.Quotient.mk_eq_zero _).mp
      rw [map_sub, Submodule.Quotient.mk_sub, he, sub_self]
    obtain ⟨j, hij, hj⟩ := X.fiberN_eventual_zero i (nx - ny) hz
    refine ⟨j, homOfLE hij, ?_⟩
    change (X.fiberD.map (homOfLE hij)).hom
      ((X.fiberDQuotEquiv i).symm (Submodule.Quotient.mk nx)) =
      (X.fiberD.map (homOfLE hij)).hom
        ((X.fiberDQuotEquiv i).symm (Submodule.Quotient.mk ny))
    apply (X.fiberDQuotEquiv j).injective
    rw [X.fiberDQuotEquiv_map_mk, X.fiberDQuotEquiv_map_mk]
    apply (Submodule.Quotient.eq _).mpr
    simpa only [map_sub] using hj

/-- (blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-module-colimit) -/
noncomputable def fiberDQuotLimitEquiv :
    (colimit X.fiberD : AddCommGrpCat.{max u v w t}) ≃+
      M ⧸ FiberSubmoduleLimitS (R := R) (S := S) (M := M) :=
  ((colimit.isColimit X.fiberD).coconePointUniqueUpToIso
    X.fiberDCoconeIsColimit).addCommGroupIsoToAddEquiv.trans AddEquiv.ulift

/-- (blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-module-colimit) -/
noncomputable def fiberDLimitEquiv :
    (colimit X.fiberD : AddCommGrpCat.{max u v w t}) ≃+
      (FiberLimitS (R := R) (S := S) ⊗[S] M) :=
  X.fiberDQuotLimitEquiv.trans
    (TensorProduct.quotTensorEquivQuotSMul M
      (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))).symm.toAddEquiv

/-- (blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-module-colimit) -/
abbrev FiberIdealLimitT : Ideal S' :=
  (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)).map (algebraMap S S')

/-- (blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-module-colimit) -/
abbrev FiberLimitT := S' ⧸ FiberIdealLimitT (R := R) (S := S) (S' := S')

omit [IsScalarTower S S' M] in
/-- (blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-module-colimit) -/
theorem fiberIdealT_limit (i : X.ι) :
    X.fiberIdealT i ≤
      (FiberIdealLimitT (R := R) (S := S) (S' := S')).comap
        (algebraMap (X.T₀ i) S') := by
  let := X.rlimit_local i
  apply Ideal.map_le_iff_le_comap.mp
  rw [fiberIdealT, Ideal.map_map, FiberIdealLimitT, Ideal.map_map]
  have h : (algebraMap (X.T₀ i) S').comp
      (algebraMap (X.R₀ i) (X.T₀ i)) =
      ((algebraMap S S').comp (algebraMap R S)).comp (algebraMap (X.R₀ i) R) := by
    rw [IsScalarTower.algebraMap_eq (X.R₀ i) (X.S₀ i) (X.T₀ i),
      ← RingHom.comp_assoc, X.st_limit_comm, RingHom.comp_assoc, X.rs_limit_comm,
      RingHom.comp_assoc]
  rw [h, ← Ideal.map_map]
  exact Ideal.map_mono (IsLocalRing.map_maximalIdeal_le (algebraMap (X.R₀ i) R))

/-- (blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-module-colimit) -/
def fiberTLimit (i : X.ι) : X.FiberT i →+* FiberLimitT (R := R) (S := S) (S' := S') :=
  Ideal.quotientMap _ (algebraMap (X.T₀ i) S') (X.fiberIdealT_limit i)

/-- (blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-module-colimit) -/
def fiberBCocone : Cocone X.fiberB where
  pt := CommRingCat.of (ULift.{max u v w} (FiberLimitT (R := R) (S := S) (S' := S')))
  ι := {
    app := fun i ↦ CommRingCat.ofHom
      (ULift.ringEquiv.symm.toRingHom.comp (X.fiberTLimit i))
    naturality := by
      intro i j f
      apply CommRingCat.hom_ext
      apply Ideal.Quotient.ringHom_ext
      ext a
      change ULift.up (Ideal.Quotient.mk _
        (algebraMap (X.T₀ j) S' (X.tmap i j (leOfHom f) a))) =
        ULift.up (Ideal.Quotient.mk _ (algebraMap (X.T₀ i) S' a))
      exact congrArg (fun s ↦ ULift.up (Ideal.Quotient.mk _ s))
        (RingHom.congr_fun (X.tlimit_comm i j (leOfHom f)) a) }

/-- (blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-module-colimit) -/
noncomputable def fiberBDesc : (colimit X.fiberB : CommRingCat.{max u v w}) →+*
    FiberLimitT (R := R) (S := S) (S' := S') :=
  ULift.ringEquiv.toRingHom.comp (colimit.desc X.fiberB X.fiberBCocone).hom

omit [IsScalarTower S S' M] in
/-- (blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-module-colimit) -/
theorem fiberBDesc_ι (i : X.ι) (b : X.FiberT i) :
    X.fiberBDesc ((colimit.ι X.fiberB i).hom b) = X.fiberTLimit i b := by
  exact congrArg ULift.down
    (ConcreteCategory.congr_hom (colimit.ι_desc X.fiberBCocone i) b)

/-- (blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-module-colimit) -/
noncomputable def fiberLimitTQuotEquiv :
    (FiberLimitT (R := R) (S := S) (S' := S') ⊗[S'] M) ≃ₗ[S]
      M ⧸ FiberSubmoduleLimitS (R := R) (S := S) (M := M) :=
  ((TensorProduct.quotTensorEquivQuotSMul M
    (FiberIdealLimitT (R := R) (S := S) (S' := S'))).restrictScalars S).trans
    ((Submodule.Quotient.restrictScalarsEquiv S
      (FiberIdealLimitT (R := R) (S := S) (S' := S') •
        (⊤ : Submodule S' M))).symm.trans
      (Submodule.quotEquivOfEq _ _ (by
        rw [FiberIdealLimitT, Ideal.smul_restrictScalars, Submodule.restrictScalars_top])))

/-- (blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-module-colimit) -/
theorem fiberLimitTQuotEquiv_tmul (a : S') (m : M) :
    fiberLimitTQuotEquiv (R := R) (S := S) (S' := S')
      (Ideal.Quotient.mk _ a ⊗ₜ[S'] m) = Submodule.Quotient.mk (a • m) := by
  simp [fiberLimitTQuotEquiv]
  rfl

omit [IsScalarTower S S' M] in
/-- (blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-module-colimit) -/
theorem fiberAEquiv_ι (i : X.ι) (a : X.FiberS i) :
    X.fiberAEquiv ((colimit.ι X.fiberA i).hom a) = X.fiberSLimit i a := by
  exact congrArg ULift.down (ConcreteCategory.congr_hom
    (colimit.isoColimitCocone_ι_hom ⟨X.fiberSCocone, X.fiberSCoconeIsColimit⟩ i) a)

/-- (blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-module-colimit) -/
theorem fiberDQuotLimitEquiv_ι (i : X.ι) (x : X.fiberD.obj i) :
    X.fiberDQuotLimitEquiv ((colimit.ι X.fiberD i).hom x) = X.fiberDLimit i x := by
  exact congrArg ULift.down (ConcreteCategory.congr_hom
    (colimit.isoColimitCocone_ι_hom ⟨X.fiberDCocone, X.fiberDCoconeIsColimit⟩ i) x)

/-- (blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-module-colimit) -/
theorem exists_limit_action :
    letI := X.fiberAct
    ∃ act : Module (colimit X.fiberB : CommRingCat.{max u v w})
      (colimit X.fiberD : AddCommGrpCat.{max u v w t}),
    letI := act
    (∀ (i : X.ι) (b : X.fiberB.obj i) (x : X.fiberD.obj i),
      (colimit.ι X.fiberD i).hom (b • x) =
        (colimit.ι X.fiberB i).hom b • (colimit.ι X.fiberD i).hom x) ∧
    (letI := Module.compHom (colimit X.fiberD : AddCommGrpCat.{max u v w t}) X.fiberψ
     ∀ a x, X.fiberDLimitEquiv (a • x) = X.fiberAEquiv a • X.fiberDLimitEquiv x) := by
  let := X.fiberAct
  let Q' := FiberLimitT (R := R) (S := S) (S' := S')
  let E := M ⧸ FiberSubmoduleLimitS (R := R) (S := S) (M := M)
  let F := fiberLimitTQuotEquiv (R := R) (S := S) (S' := S') (M := M)
  let actQ : Module Q' E := F.symm.toAddEquiv.module Q'
  let := actQ
  have hQ (b : S') (m : M) : (Ideal.Quotient.mk _ b : Q') •
      (Submodule.Quotient.mk m : E) = Submodule.Quotient.mk (b • m) := by
    change F ((Ideal.Quotient.mk _ b : Q') • F.symm (Submodule.Quotient.mk m)) =
      (Submodule.Quotient.mk (b • m) : E)
    have he : F.symm (Submodule.Quotient.mk m) = (1 : Q') ⊗ₜ[S'] m := by
      apply F.injective
      simpa [F] using (fiberLimitTQuotEquiv_tmul (R := R) (S := S) (S' := S') 1 m).symm
    rw [he, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    exact fiberLimitTQuotEquiv_tmul b m
  let actE : Module (colimit X.fiberB : CommRingCat.{max u v w}) E :=
    Module.compHom E X.fiberBDesc
  let := actE
  let act : Module (colimit X.fiberB : CommRingCat.{max u v w})
      (colimit X.fiberD : AddCommGrpCat.{max u v w t}) :=
    X.fiberDQuotLimitEquiv.module _
  let := act
  refine ⟨act, ?_, ?_⟩
  · intro i b x
    apply X.fiberDQuotLimitEquiv.injective
    change X.fiberDQuotLimitEquiv ((colimit.ι X.fiberD i).hom (b • x)) =
      X.fiberDQuotLimitEquiv (X.fiberDQuotLimitEquiv.symm
        (X.fiberBDesc ((colimit.ι X.fiberB i).hom b) •
          X.fiberDQuotLimitEquiv ((colimit.ι X.fiberD i).hom x)))
    rw [AddEquiv.apply_symm_apply, X.fiberDQuotLimitEquiv_ι,
      X.fiberDQuotLimitEquiv_ι, X.fiberBDesc_ι]
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨q, rfl⟩ := (X.fiberDQuotEquiv i).symm.surjective x
    obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [X.fiberDQuotEquiv_symm_mk]
    change X.fiberDLimit i (ULift.up (Ideal.Quotient.mk _ b • (1 ⊗ₜ[X.T₀ i] n))) = _
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [X.fiberDLimit_tmul]
    have he := X.fiberDLimit_tmul i 1 n
    simp only [map_one, one_smul] at he
    rw [he]
    have hb : X.fiberTLimit i (Ideal.Quotient.mk _ b) =
        (Ideal.Quotient.mk _ (algebraMap (X.T₀ i) S' b) : Q') := rfl
    rw [hb, hQ, X.nlimit_smul]
  · let := Module.compHom (colimit X.fiberD : AddCommGrpCat.{max u v w t}) X.fiberψ
    intro a x
    obtain ⟨i, ai, hai⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves (forget CommRingCat) (colimit.isColimit X.fiberA)) a
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective ai
    obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective _ (X.fiberDQuotLimitEquiv x)
    subst a
    let H := TensorProduct.quotTensorEquivQuotSMul M
      (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R))
    change H.symm (X.fiberDQuotLimitEquiv (X.fiberDQuotLimitEquiv.symm
      (X.fiberBDesc (X.fiberψ ((colimit.ι X.fiberA i).hom
        (Ideal.Quotient.mk _ s))) • X.fiberDQuotLimitEquiv x))) =
      X.fiberAEquiv ((colimit.ι X.fiberA i).hom (Ideal.Quotient.mk _ s)) •
        H.symm (X.fiberDQuotLimitEquiv x)
    rw [AddEquiv.apply_symm_apply, ← hm]
    have hψ := RingHom.congr_fun (X.fiberψ_comp_ι i) (Ideal.Quotient.mk _ s)
    change X.fiberψ ((colimit.ι X.fiberA i).hom (Ideal.Quotient.mk _ s)) =
      (colimit.ι X.fiberB i).hom (X.fiberφ i (Ideal.Quotient.mk _ s)) at hψ
    rw [hψ, X.fiberBDesc_ι, X.fiberAEquiv_ι]
    change H.symm ((Ideal.Quotient.mk _
      (algebraMap (X.T₀ i) S' (algebraMap (X.S₀ i) (X.T₀ i) s)) : Q') •
        (Submodule.Quotient.mk m : E)) =
      Ideal.Quotient.mk _ (algebraMap (X.S₀ i) S s) • H.symm (Submodule.Quotient.mk m)
    have hs := RingHom.congr_fun (X.st_limit_comm i) s
    change algebraMap (X.T₀ i) S' (algebraMap (X.S₀ i) (X.T₀ i) s) =
      algebraMap S S' (algebraMap (X.S₀ i) S s) at hs
    rw [hs, hQ, algebraMap_smul, Submodule.Quotient.mk_smul]
    rw [H.symm.map_smul]
    rw [← Ideal.Quotient.algebraMap_eq]
    exact (algebraMap_smul (FiberLimitS (R := R) (S := S))
      (algebraMap (X.S₀ i) S s) (H.symm (Submodule.Quotient.mk m))).symm

end Module.NoetherianLocalModelTower

namespace Module

/-- The module colimit of the explicit closed-fibre system, with its scalar action.

Source: Stacks Project, Algebra, Tag 00R7, quotient systems before the second use of 00R6.
(blueprint: lem-weil-pbc-noetherian-local-model-tower-fiber-module-colimit)

Proof: First derive S_i-semilinearity of nmap and nlimit from their T_i
semilinearity and the commuting middle-to-top squares. The images of the
submodules m_i N_i form an S-submodule of M: move summands and scalars to a
common stage using directedness and slimit_surj. It contains m_R M: the proved
fiberIdealS_limit_rep represents each coefficient in m_R S at a stage, and
nlimit_surj represents each module element. Thus every element of m_R M has
a stage representative in m_i N_i. Using nlimit_eq at a further stage proves
that a stage element killed in M/m_R M is killed in its later stage quotient.

Identify each fiberD_i with N_i/m_i N_i using fiberDEquiv and
quotTensorEquivQuotSMul. Descend nlimit to an additive map from this quotient
to M/m_R M. Its formula on pure tensors and the original nlimit_comm make
these maps a cocone. Surjectivity follows from nlimit_surj. The eventual-zero
result, applied to differences, proves eventual equality. The types filtered
colimit criterion and reflection by forget AddCommGrpCat identify this cocone
as a group colimit. Compose the colimit comparison with the inverse of
quotTensorEquivQuotSMul for S/m_R S to construct fiberDLimitEquiv.

Construct the ring cocone from fiberB to S'/m_R S' by descending its limit
maps, and let fiberBDesc be its universal ring homomorphism from colimit B.
No assertion that this ring cocone is a colimit is needed. The equivalence
between the top quotient tensor module and M/m_R M follows by restricting
the top ideal-times-module quotient to S and using Ideal.smul_restrictScalars.
Transport its module action to M/m_R M, restrict along fiberBDesc, and transport
across the proved additive colimit comparison to define the required action.
The quotient formula mk(b) acting on mk(m) equals mk(b acting on m); applying
it to pure tensors proves coprojection semilinearity using nlimit_smul.

Finally represent any colimit-A scalar at a stage and any quotient module
element by an element of M. The coprojection formula for fiberPsi and
st_limit_comm identify its image under fiberBDesc with the image of the
canonical fiberAEquiv in the top quotient. The quotient action formula,
algebraMap_smul, and S-linearity of the tensor-quotient equivalence give the
asserted scalar compatibility. Package this action and fiberDLimitEquiv.
All data are explicit or obtained from a proved universal property; no
flatness, tlimit_surj or tlimit_eq is used.
-/
theorem NoetherianLocalModelTower.fiber_module_colimit
    {R : Type u} {S : Type v} {S' : Type w} {M : Type t}
    [CommRing R] [CommRing S] [CommRing S'] [IsLocalRing R] [AddCommGroup M]
    [Algebra R S] [Algebra S S'] [Module S' M] [Module S M]
    [IsScalarTower S S' M]
    (X : NoetherianLocalModelTower R S S' M) :
    letI := X.preorder
    letI := X.commR
    letI := X.commS
    letI := X.localR
    letI := X.algRS
    letI := X.addN
    letI := X.moduleS
    let B := X.fiberB
    let D := X.fiberD
    letI := X.fiberAct
    let ψ := X.fiberψ
    ∃ limitAct : Module (colimit B : CommRingCat.{max u v w})
      (colimit D : AddCommGrpCat.{max u v w t}),
    letI := limitAct
    (∀ (i : X.ι) (b : B.obj i) (x : D.obj i),
      (colimit.ι D i).hom (b • x) = (colimit.ι B i).hom b • (colimit.ι D i).hom x) ∧
    (∃
      (eD : (colimit D : AddCommGrpCat.{max u v w t}) ≃+
        ((S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)) ⊗[S] M)),
      letI := Module.compHom (colimit D : AddCommGrpCat.{max u v w t}) ψ
      ∀ a x, eD (a • x) = X.fiberAEquiv a • eD x) := by
  let := X.preorder
  let := X.commR
  let := X.commS
  let := X.localR
  let := X.algRS
  let := X.addN
  let := X.moduleS
  let := X.fiberAct
  obtain ⟨act, hsem, hcompat⟩ := X.exists_limit_action
  exact ⟨act, hsem, X.fiberDLimitEquiv, hcompat⟩

end Module
