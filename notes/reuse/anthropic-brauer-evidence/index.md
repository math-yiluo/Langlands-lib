# Brauer audit reproducible evidence

This appendix supports [the audit](../anthropic-brauer-audit.md). No file here is an accepted Lean proof. Experimental Lean remains private; the fenced recipes below reconstruct the bounded experiments.

## Terminal reports

The table separates service success, build process exit status, and error/warning counts. Consult complete reports for declaration inspection and all informational output. Warnings vary with rebuilt dependencies.

| Report | Service `ok` | Build exit | Errors / warnings |
| --- | --- | --- | --- |
| [`71969c39-c3fa-4dae-b588-d8bc93d53ac6`](71969c39-c3fa-4dae-b588-d8bc93d53ac6.md) | `false` | 1 | 1 / 5 |
| [`0a52edfb-2556-443c-915f-b0374d866ef0`](0a52edfb-2556-443c-915f-b0374d866ef0.md) | `false` | 1 | 2 / 39 |
| [`c7df1a9f-2ac4-45ac-a534-b7720efe1fa2`](c7df1a9f-2ac4-45ac-a534-b7720efe1fa2.md) | `false` | 1 | 1 / 36 |
| [`97980068-d161-4f21-9824-5ff5a543133a`](97980068-d161-4f21-9824-5ff5a543133a.md) | `false` | 1 | 1 / 30 |
| [`4d218106-a903-4467-9b9d-92a576141c2b`](4d218106-a903-4467-9b9d-92a576141c2b.md) | `true` | 0 | 0 / 10 |
| [`813e2448-4278-4ca5-9a57-f1c49409d1f2`](813e2448-4278-4ca5-9a57-f1c49409d1f2.md) | `false` | 1 | 4 / 1 |
| [`63b0c413-d9ca-4c8b-9b51-ac83307704f5`](63b0c413-d9ca-4c8b-9b51-ac83307704f5.md) | `true` | 0 | 0 / 0 |
| [`5bab0732-36c7-4627-8d82-e253c503897e`](5bab0732-36c7-4627-8d82-e253c503897e.md) | `false` | 0 | 0 / 46 |
| [`ff9426d5-6c84-4f22-865c-eff614d87b0b`](ff9426d5-6c84-4f22-865c-eff614d87b0b.md) | `true` | 0 | 0 / 0 |
| [`75c17d9b-4b2b-44e6-a6d0-2dc3f75e9181`](75c17d9b-4b2b-44e6-a6d0-2dc3f75e9181.md) | `true` | 0 | 0 / 0 |

The first four checks record source compatibility failures. `4d218106-a903-4467-9b9d-92a576141c2b` successfully checked the adapted source before added modification comments. `813e2448-4278-4ca5-9a57-f1c49409d1f2` records the initial bridge elaboration failure; `63b0c413-d9ca-4c8b-9b51-ac83307704f5` is the repaired bridge check. `5bab0732-36c7-4627-8d82-e253c503897e` successfully rebuilt both modules but attempted root inspection in `BrauerAudit.Bridges`, which does not import the root; its inspection failed with unknown constant. `ff9426d5-6c84-4f22-865c-eff614d87b0b` corrects that inspection using `BrauerAudit.Inspect`. `75c17d9b-4b2b-44e6-a6d0-2dc3f75e9181` checks the complete unapplied API inventory and re-inspects the two-universe induction-sum transport. All successful reports still have `proof_accepted: false`.

One interrupted restart call had no Lean diagnostic report. The retained terminal service-job status below records cancellation; it is neither a source failure nor a successful compile.

```json
{
  "id": "e2cc999474dd4144bf0df5e88a731982",
  "state": "done",
  "outcome": "cancelled",
  "definitive": 0,
  "submitted_at": 1792936242.8687267,
  "started_at": null,
  "finished_at": 1792936531.311897
}
```

## Source manifest and closure

The closure follows textual imports from both listed roots and stops at Mathlib and Lean. All eight listed files were read in full. `nonlocal: []` means no further unresolved local import, not that Mathlib has no dependencies. Their source lines total 2,099. These are file-level boundaries, not a minimal declaration dependency closure.

```json
{
  "source": "/home/taskhub/pilot/literature/Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2",
  "roots": [
    "Theorems.Thm_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter",
    "P2M.Sol.S_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter"
  ],
  "modules": {
    "Theorems.Thm_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter": {
      "path": "Theorems/Thm_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter.lean",
      "sha256": "e95c9ec70037c816a43048d4d94006ae45547f23ab90b31f78ff02204f37df91",
      "lines": 16,
      "imports": [
        "Mathlib",
        "P2M.Util",
        "P2M.Sol.S_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter"
      ]
    },
    "P2M.Util": {
      "path": "P2M/Util.lean",
      "sha256": "66f62069b83c0cf97531f88e5bd2c249e471df011ad873b0bd034eb959b1d8da",
      "lines": 127,
      "imports": [
        "Lean"
      ]
    },
    "P2M.Sol.S_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter": {
      "path": "P2M/Sol/S_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter.lean",
      "sha256": "5babda630f44302983a1103552efde23e363517bfd56c9c8cd55ddf797c6f0c2",
      "lines": 185,
      "imports": [
        "Mathlib",
        "Definitions.Def_ClassFunction_Induced",
        "Theorems.Thm_ClassFunction_exists_one_eq_sum_zsmul_induced_one_of_hyperelementary",
        "Theorems.Thm_ClassFunction_exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem",
        "P2M.Util"
      ]
    },
    "Definitions.Def_ClassFunction_Induced": {
      "path": "Definitions/Def_ClassFunction_Induced.lean",
      "sha256": "44cee0b2389dc811a40237bd840ed7ad22cb56179202ed494a04427ecb0e0e48",
      "lines": 212,
      "imports": [
        "Mathlib"
      ]
    },
    "Theorems.Thm_ClassFunction_exists_one_eq_sum_zsmul_induced_one_of_hyperelementary": {
      "path": "Theorems/Thm_ClassFunction_exists_one_eq_sum_zsmul_induced_one_of_hyperelementary.lean",
      "sha256": "b3da88e645813c9c397fb8dff750e595a4d2ebb1a4ff73a13fe0478a346bdc2f",
      "lines": 13,
      "imports": [
        "Mathlib",
        "Definitions.Def_ClassFunction_Induced",
        "P2M.Util",
        "P2M.Sol.S_ClassFunction_exists_one_eq_sum_zsmul_induced_one_of_hyperelementary"
      ]
    },
    "P2M.Sol.S_ClassFunction_exists_one_eq_sum_zsmul_induced_one_of_hyperelementary": {
      "path": "P2M/Sol/S_ClassFunction_exists_one_eq_sum_zsmul_induced_one_of_hyperelementary.lean",
      "sha256": "0a4c9870da3024ff6f7fdc7d3d38320b165041737461f49831daba54ee50d2f7",
      "lines": 660,
      "imports": [
        "Mathlib",
        "Definitions.Def_ClassFunction_Induced",
        "P2M.Util"
      ]
    },
    "Theorems.Thm_ClassFunction_exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem": {
      "path": "Theorems/Thm_ClassFunction_exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem.lean",
      "sha256": "05246d0bca87942fa628d5e4f5640246ad1055c3cf2e2c07c773f490dd2bd715",
      "lines": 19,
      "imports": [
        "Mathlib",
        "Definitions.Def_ClassFunction_Induced",
        "P2M.Util",
        "P2M.Sol.S_ClassFunction_exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem"
      ]
    },
    "P2M.Sol.S_ClassFunction_exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem": {
      "path": "P2M/Sol/S_ClassFunction_exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem.lean",
      "sha256": "910c22f00318287de2d1eb773450fdc51522dfa63ba5df2e50624f908557f3bb",
      "lines": 867,
      "imports": [
        "Mathlib",
        "Definitions.Def_ClassFunction_Induced",
        "P2M.Util"
      ]
    }
  },
  "nonlocal": []
}
```

## Final adaptation manifest

No module or declaration was renamed. Wrapper theorem, `P2MW...solution`, and helper names retain their upstream names. The four changed source files carry Worker 18 modification notices; original and final bytes are bound below.

```json
[
  {
    "module": "Theorems.Thm_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter",
    "path": "Theorems/Thm_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter.lean",
    "original_sha256": "e95c9ec70037c816a43048d4d94006ae45547f23ab90b31f78ff02204f37df91",
    "adapted_sha256": "e95c9ec70037c816a43048d4d94006ae45547f23ab90b31f78ff02204f37df91"
  },
  {
    "module": "P2M.Util",
    "path": "P2M/Util.lean",
    "original_sha256": "66f62069b83c0cf97531f88e5bd2c249e471df011ad873b0bd034eb959b1d8da",
    "adapted_sha256": "66f62069b83c0cf97531f88e5bd2c249e471df011ad873b0bd034eb959b1d8da"
  },
  {
    "module": "P2M.Sol.S_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter",
    "path": "P2M/Sol/S_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter.lean",
    "original_sha256": "5babda630f44302983a1103552efde23e363517bfd56c9c8cd55ddf797c6f0c2",
    "adapted_sha256": "cdcb514b0fb0c04381d0e14a66ee3b252c3f1781965780f2e5b8f519ebfab248"
  },
  {
    "module": "Definitions.Def_ClassFunction_Induced",
    "path": "Definitions/Def_ClassFunction_Induced.lean",
    "original_sha256": "44cee0b2389dc811a40237bd840ed7ad22cb56179202ed494a04427ecb0e0e48",
    "adapted_sha256": "09a2f151e87d9d856e53c036b86f77a4165c9943deab1513a033b12ddbcbe59d"
  },
  {
    "module": "Theorems.Thm_ClassFunction_exists_one_eq_sum_zsmul_induced_one_of_hyperelementary",
    "path": "Theorems/Thm_ClassFunction_exists_one_eq_sum_zsmul_induced_one_of_hyperelementary.lean",
    "original_sha256": "b3da88e645813c9c397fb8dff750e595a4d2ebb1a4ff73a13fe0478a346bdc2f",
    "adapted_sha256": "b3da88e645813c9c397fb8dff750e595a4d2ebb1a4ff73a13fe0478a346bdc2f"
  },
  {
    "module": "P2M.Sol.S_ClassFunction_exists_one_eq_sum_zsmul_induced_one_of_hyperelementary",
    "path": "P2M/Sol/S_ClassFunction_exists_one_eq_sum_zsmul_induced_one_of_hyperelementary.lean",
    "original_sha256": "0a4c9870da3024ff6f7fdc7d3d38320b165041737461f49831daba54ee50d2f7",
    "adapted_sha256": "4b4417e6772abd3cb47484ecee1950bfcd34996ea184654917a363c0a1cc42aa"
  },
  {
    "module": "Theorems.Thm_ClassFunction_exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem",
    "path": "Theorems/Thm_ClassFunction_exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem.lean",
    "original_sha256": "05246d0bca87942fa628d5e4f5640246ad1055c3cf2e2c07c773f490dd2bd715",
    "adapted_sha256": "05246d0bca87942fa628d5e4f5640246ad1055c3cf2e2c07c773f490dd2bd715"
  },
  {
    "module": "P2M.Sol.S_ClassFunction_exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem",
    "path": "P2M/Sol/S_ClassFunction_exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem.lean",
    "original_sha256": "910c22f00318287de2d1eb773450fdc51522dfa63ba5df2e50624f908557f3bb",
    "adapted_sha256": "9c6f971f0e8c30b15268a225141e586be8b2d2e7babe98897a823e733e2e6c9d"
  }
]
```

## Exact final compatibility patch

Apply to the eight original modules in an isolated private draft. It includes all final source changes; abandoned attempts are diagnosed in the terminal reports. No upstream wrapper or utility was removed.

```diff
--- upstream/P2M/Sol/S_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter.lean
+++ adapted/P2M/Sol/S_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter.lean
@@ -1,3 +1,7 @@
+/- Modified by Worker 18 for the private 2026-10-25 compatibility audit.
+Original: Anthropic FLT 6e837e75355538c7f80bab5b956861e86c4eacc2.
+Copyright 2026 Anthropic, PBC; Apache-2.0. See retained LICENSE, NOTICE
+and the paired Markdown for the exact compatibility changes. -/
 import Mathlib
 import Definitions.Def_ClassFunction_Induced
 import Theorems.Thm_ClassFunction_exists_one_eq_sum_zsmul_induced_one_of_hyperelementary
@@ -124,7 +128,8 @@
   apply congrFun (ClassFunction.induced_congr _ ?_) g
   intro y hy
   obtain ⟨z, hz, rfl⟩ := hy
-  simp only [Subgroup.coe_subtype]
+  change (if hg : (z : G) ∈ H then extH j ⟨(z : G), hg⟩ else 0) =
+    ext (L' j) (ψ' j) (z : G)
   rw [dif_pos z.2]
   have hz' : (⟨(z : G), z.2⟩ : H) ∈ L j := by simpa using hz
   have hmem : (z : G) ∈ L' j := ⟨z, hz, rfl⟩
--- upstream/Definitions/Def_ClassFunction_Induced.lean
+++ adapted/Definitions/Def_ClassFunction_Induced.lean
@@ -1,4 +1,9 @@
 import Mathlib
+
+/- Modified by Worker 18 for the private 2026-10-25 compatibility audit.
+Original: Anthropic FLT 6e837e75355538c7f80bab5b956861e86c4eacc2,
+Copyright 2026 Anthropic, PBC; Apache-2.0 (retained LICENSE and NOTICE).
+The conjugation proof closes the residual definitional equality explicitly. -/
 
 set_option autoImplicit false
 
@@ -39,6 +44,7 @@
   refine Fintype.sum_equiv (Equiv.mulLeft y) _ _ fun x => ?_
   have : x⁻¹ * (y⁻¹ * g * y) * x = (y * x)⁻¹ * g * (y * x) := by group
   simp only [Equiv.coe_mulLeft, this]
+  rfl
 
 theorem induced_add (H : Subgroup G) (φ ψ : G → K) :
     induced H (φ + ψ) = induced H φ + induced H ψ := by
--- upstream/P2M/Sol/S_ClassFunction_exists_one_eq_sum_zsmul_induced_one_of_hyperelementary.lean
+++ adapted/P2M/Sol/S_ClassFunction_exists_one_eq_sum_zsmul_induced_one_of_hyperelementary.lean
@@ -1,3 +1,7 @@
+/- Modified by Worker 18 for the private 2026-10-25 compatibility audit.
+Original: Anthropic FLT 6e837e75355538c7f80bab5b956861e86c4eacc2.
+Copyright 2026 Anthropic, PBC; Apache-2.0. See retained LICENSE, NOTICE
+and the paired Markdown for the exact compatibility changes. -/
 import Mathlib
 import Definitions.Def_ClassFunction_Induced
 import P2M.Util
@@ -524,7 +528,7 @@
       Subtype.val_injective
   haveI : Algebra.IsIntegral ℤ R := Algebra.IsIntegral.of_finite ℤ R
   have hcomap : (𝔪.comap (algebraMap ℤ R)).IsMaximal :=
-    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝔪
+    Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := ℤ) 𝔪
   have hp0 : p ≠ 0 := by
     rintro rfl
     haveI : CharZero (R ⧸ 𝔪) := CharP.charP_to_charZero (R ⧸ 𝔪)
--- upstream/P2M/Sol/S_ClassFunction_exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem.lean
+++ adapted/P2M/Sol/S_ClassFunction_exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem.lean
@@ -1,3 +1,7 @@
+/- Modified by Worker 18 for the private 2026-10-25 compatibility audit.
+Original: Anthropic FLT 6e837e75355538c7f80bab5b956861e86c4eacc2.
+Copyright 2026 Anthropic, PBC; Apache-2.0. See retained LICENSE, NOTICE
+and the paired Markdown for the exact compatibility changes. -/
 import Mathlib
 import Definitions.Def_ClassFunction_Induced
 import P2M.Util
@@ -68,13 +72,15 @@
 theorem extChar_lift (H : Subgroup K) (e : Entry H) (g : K) (hg : g ∈ e.1.map H.subtype) :
     extChar (lift H e).1 (lift H e).2 g = if hg' : g ∈ H then extChar e.1 e.2 ⟨g, hg'⟩ else 0 := by
   obtain ⟨z, hz, rfl⟩ := hg
-  simp only [Subgroup.coe_subtype]
+  change extChar (lift H e).1 (lift H e).2 (z : K) =
+    if hg' : (z : K) ∈ H then extChar e.1 e.2 ⟨(z : K), hg'⟩ else 0
   rw [dif_pos z.2]
   have hz' : (⟨(z : K), z.2⟩ : H) ∈ e.1 := by simpa using hz
   have hmem : (z : K) ∈ (lift H e).1 := ⟨z, hz, rfl⟩
   simp only [extChar, dif_pos hz', dif_pos hmem, lift_snd_apply]
   congr 2
   apply (e.1.equivMapOfInjective H.subtype H.subtype_injective).injective
+  dsimp only [lift] at hmem ⊢
   rw [MulEquiv.apply_symm_apply]
   apply Subtype.ext
   rfl
```

## Check recipes

Copy the eight files above, preserve the notices in [source notices](notices.md), apply the patch, and create the three inspection files below. Every private Lean file also needs English same-stem Markdown. Use the project Lean service with environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, never a shell Lean executable. The final API module imports both roots of the experiment.

```json
{
  "operation": "lean_check",
  "arguments": {
    "environment_artifact": "3b864ddf-f0af-4c18-8903-c6f813a0ce0f",
    "modules": [
      "BrauerAudit.Inspect"
    ],
    "directory": ".private/drafts/brauer-audit",
    "declaration": "BrauerInduction.exists_trace_eq_sum_zsmul_induced_linearCharacter"
  }
}
```

```json
{
  "operation": "lean_check",
  "arguments": {
    "environment_artifact": "3b864ddf-f0af-4c18-8903-c6f813a0ce0f",
    "modules": [
      "BrauerAudit.API"
    ],
    "directory": ".private/drafts/brauer-audit",
    "declaration": "BrauerAudit.inducedTransport"
  }
}
```

### `BrauerAudit/Inspect.lean`

SHA256 `203d4d31260c48107359dbac1e7f020139cb1c42248c3b4079f0451c7732ff18`.

```lean
import Theorems.Thm_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter
set_option pp.universes true
set_option pp.explicit true
set_option pp.proofs false
#check @BrauerInduction.exists_trace_eq_sum_zsmul_induced_linearCharacter
#print axioms BrauerInduction.exists_trace_eq_sum_zsmul_induced_linearCharacter
#check @ClassFunction.exists_one_eq_sum_zsmul_induced_one_of_hyperelementary
#print axioms ClassFunction.exists_one_eq_sum_zsmul_induced_one_of_hyperelementary
#check @ClassFunction.exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem
#print axioms ClassFunction.exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem
```

#### Private source declaration inspection

Print complete unapplied root signatures and transitive axiom lists for the three external theorem wrappers. Does not establish semantic acceptance or host target coverage.


### `BrauerAudit/Bridges.lean`

SHA256 `11305a31430cf4db40015ed0396b10f9c31d211f7b76a53dfcb1fde7f6f50839`.

```lean
import Mathlib
import Definitions.Def_ClassFunction_Induced
import Langlands.Representation.Finite.BrauerStatement

noncomputable section
open scoped MatrixGroups Classical
open Langlands.FiniteRep
namespace BrauerAudit
universe u v w

variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V]
  [Module ℂ V] [Module.Finite ℂ V]

def matrixModel (ρ : Representation ℂ G V) :
    G →* GL (Fin (Module.finrank ℂ V)) ℂ :=
  (Units.map (LinearMap.toMatrixAlgEquiv (Module.finBasis ℂ V)).toMonoidHom).comp
    ρ.asGroupHom

theorem matrixModel_trace (ρ : Representation ℂ G V) (g : G) :
    ((matrixModel ρ g : GL (Fin (Module.finrank ℂ V)) ℂ) :
      Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ).trace =
      ρ.character g := by
  exact (LinearMap.trace_eq_matrix_trace ℂ (Module.finBasis ℂ V) (ρ g)).symm

theorem smallGroup [Finite G] :
    ∃ (K : Type) (_ : Group K) (_ : Fintype K), Nonempty (G ≃* K) :=
  Finite.exists_type_univ_nonempty_mulEquiv G

variable {K : Type w} [Group K]

theorem subgroupCard (e : G ≃* K) (S : Subgroup K) :
    Nat.card (S.comap e.toMonoidHom) = Nat.card S := by
  change Nat.card (S.comap (e : G →* K)) = Nat.card S
  rw [Subgroup.comap_equiv_eq_map_symm]
  exact Subgroup.card_map_of_injective e.symm.injective

theorem inducedTransport [Fintype G] [Fintype K] (e : G ≃* K)
    (S : Subgroup K) (f : K → ℂ) (g : G) :
    ClassFunction.induced (S.comap e.toMonoidHom) (f ∘ e) g =
      ClassFunction.induced S f (e g) := by
  classical
  rw [ClassFunction.induced_apply, ClassFunction.induced_apply, subgroupCard e S]
  congr 1
  refine Fintype.sum_equiv e.toEquiv _ _ fun x => ?_
  simp only [Subgroup.mem_comap, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    map_mul, map_inv, Function.comp_apply]
  rfl

/-- Conditional: this does not prove the assumed actual-induction formula. -/
theorem rankOneBridge [Fintype G] (h : FiniteInducedCharacterFormulaStatement G)
    (S : Subgroup G) (χ : S →* ℂˣ) (g : G) :
    inducedCharacter (⟨S, χ⟩ : MonomialDatum ℂ G) g =
      ClassFunction.induced S (fun y => if hy : y ∈ S then (χ ⟨y, hy⟩ : ℂ) else 0) g := by
  classical
  change (induceRep S (oneDimensional χ)).character g = _
  rw [h S (oneDimensional χ) g, ClassFunction.induced_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp [character_oneDimensional]

end BrauerAudit
set_option pp.universes true
#check @BrauerAudit.matrixModel_trace
#print axioms BrauerAudit.matrixModel_trace
#check @BrauerAudit.smallGroup
#print axioms BrauerAudit.smallGroup
#check @BrauerAudit.subgroupCard
#print axioms BrauerAudit.subgroupCard
#check @BrauerAudit.inducedTransport
#print axioms BrauerAudit.inducedTransport
#check @BrauerAudit.rankOneBridge
#print axioms BrauerAudit.rankOneBridge
```

#### Private bridge feasibility experiments

Worker 18's internal audit experiments, derived from the pinned Mathlib APIs and the published Library interfaces. No new theorem from external literature is asserted. Matrix transport uses the finite basis, units of the matrix algebra equivalence and trace invariance. Group transport uses Mathlib's arbitrary-universe finite-group equivalence; subgroup cardinality uses injectivity, and the normalized sum is reindexed by the group equivalence. The final rank-one bridge explicitly assumes `FiniteInducedCharacterFormulaStatement G`, specializes it to the existing scalar representation and evaluates its trace. It does not discharge that hypothesis or prove the Library Brauer targets. All experiments preserve separate group and representation-carrier universes.


### `BrauerAudit/API.lean`

SHA256 `a3e2185ad9cee79a99b6b40c64e399d0e8daecccf7e54b26af6b75c149816f39`.

```lean
import BrauerAudit.Bridges
import BrauerAudit.Inspect
set_option pp.universes true
#check @Langlands.FiniteRep.ofRepresentation
#check @Langlands.FiniteRep.modelEquiv
#check @Langlands.FiniteRep.classOfRepresentation
#check @Langlands.FiniteRep.classOfRepresentation_eq_iff
#check @Langlands.FiniteRep.character_classOfRepresentation
#check @Langlands.FiniteRep.induceRepEquiv
#check @Langlands.FiniteRep.character_induce_classOf
#check @Langlands.FiniteRep.virtualRep_exists_difference
#check @Langlands.FiniteRep.virtualCharacter_ofClass
#check @Langlands.FiniteRep.mem_virtualCharacters_iff
#check @Langlands.FiniteRep.character_oneDimensional
#check @Langlands.FiniteRep.inducedCharacterLattice_le
#check @Langlands.FiniteRep.FiniteInducedCharacterFormulaStatement
#check @Langlands.FiniteRep.FiniteVirtualCharacterFaithfulnessStatement
#check @Langlands.FiniteRep.IntegralBrauerCharacterLatticeStatement
#check @Langlands.FiniteRep.IntegralBrauerSpanningStatement
#check @Finite.exists_type_univ_nonempty_mulEquiv
#check @LinearMap.toMatrixAlgEquiv
#check @Representation.asGroupHom
#check @LinearMap.trace_eq_matrix_trace
#check @Subgroup.card_map_of_injective
#check @Fintype.sum_equiv
#check @Representation.char_iso
#check @BrauerInduction.exists_trace_eq_sum_zsmul_induced_linearCharacter
#check @ClassFunction.exists_one_eq_sum_zsmul_induced_one_of_hyperelementary
#check @ClassFunction.exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem
```

#### Private full API inventory

Worker 18 checks unapplied declarations with universe printing, for the audit only. This imports both experiments and the adapted source closure; it proves no additional statement.


## Full displayed types and axiom output

The complete service JSON reports above retain all stdout, stderr, inspection metadata, type fingerprints and diagnostics. For reading convenience, the following text is extracted without shortening from their informational messages. The inspection service removed temporary raw expression files before they could be copied: their hashes and byte counts survive, but the raw `repr` expressions themselves are unavailable. We do not claim to retain them. Source declaration telescopes and full unapplied printed types remain available.

### `4d218106-a903-4467-9b9d-92a576141c2b`

```text
info: source/BrauerAudit/Inspect.lean:5:0: @BrauerInduction.exists_trace_eq_sum_zsmul_induced_linearCharacter : ∀ {G : Type} [inst : Group.{0} G]
  [inst_1 : Fintype.{0} G] {n : Nat}
  (ρ :
    @MonoidHom.{0, 0} G
      (@Matrix.GeneralLinearGroup.{0, 0} (Fin n) Complex (instDecidableEqFin n) (Fin.fintype n) Complex.instSemiring)
      (@MulOneClass.toMulOne.{0} G
        (@Monoid.toMulOneClass.{0} G (@DivInvMonoid.toMonoid.{0} G (@Group.toDivInvMonoid.{0} G inst))))
      (@MulOneClass.toMulOne.{0}
        (@Matrix.GeneralLinearGroup.{0, 0} (Fin n) Complex (instDecidableEqFin n) (Fin.fintype n) Complex.instSemiring)
        (@Units.instMulOneClass.{0} (Matrix.{0, 0, 0} (Fin n) (Fin n) Complex)
          (@Semiring.toMonoid.{0} (Matrix.{0, 0, 0} (Fin n) (Fin n) Complex)
            (@Matrix.semiring.{0, 0} (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))),
  ∃ k H ψ a,
    ∀ (g : G),
      @Eq.{1} Complex
        (@Matrix.trace.{0, 0} (Fin n) Complex (Fin.fintype n) Complex.instAddCommMonoid
          (@Units.val.{0} (Matrix.{0, 0, 0} (Fin n) (Fin n) Complex)
            (@Semiring.toMonoid.{0} (Matrix.{0, 0, 0} (Fin n) (Fin n) Complex)
              (@Matrix.semiring.{0, 0} (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))
            (@DFunLike.coe.{1, 1, 1}
              (@MonoidHom.{0, 0} G
                (@Matrix.GeneralLinearGroup.{0, 0} (Fin n) Complex (instDecidableEqFin n) (Fin.fintype n)
                  Complex.instSemiring)
                (@MulOneClass.toMulOne.{0} G
                  (@Monoid.toMulOneClass.{0} G (@DivInvMonoid.toMonoid.{0} G (@Group.toDivInvMonoid.{0} G inst))))
                (@MulOneClass.toMulOne.{0}
                  (@Matrix.GeneralLinearGroup.{0, 0} (Fin n) Complex (instDecidableEqFin n) (Fin.fintype n)
                    Complex.instSemiring)
                  (@Units.instMulOneClass.{0} (Matrix.{0, 0, 0} (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid.{0} (Matrix.{0, 0, 0} (Fin n) (Fin n) Complex)
                      (@Matrix.semiring.{0, 0} (Fin n) Complex Complex.instSemiring (Fin.fintype n)
                        (instDecidableEqFin n))))))
              G
              (fun x =>
                @Matrix.GeneralLinearGroup.{0, 0} (Fin n) Complex (instDecidableEqFin n) (Fin.fintype n)
                  Complex.instSemiring)
              (@MonoidHom.instFunLike.{0, 0} G
                (@Matrix.GeneralLinearGroup.{0, 0} (Fin n) Complex (instDecidableEqFin n) (Fin.fintype n)
                  Complex.instSemiring)
                (@MulOneClass.toMulOne.{0} G
                  (@Monoid.toMulOneClass.{0} G (@DivInvMonoid.toMonoid.{0} G (@Group.toDivInvMonoid.{0} G inst))))
                (@MulOneClass.toMulOne.{0}
                  (@Matrix.GeneralLinearGroup.{0, 0} (Fin n) Complex (instDecidableEqFin n) (Fin.fintype n)
                    Complex.instSemiring)
                  (@Units.instMulOneClass.{0} (Matrix.{0, 0, 0} (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid.{0} (Matrix.{0, 0, 0} (Fin n) (Fin n) Complex)
                      (@Matrix.semiring.{0, 0} (Fin n) Complex Complex.instSemiring (Fin.fintype n)
                        (instDecidableEqFin n))))))
              ρ g)))
        (∑ i,
          @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
            (@Int.cast.{0} Complex Complex.instIntCast (a i))
            (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
              (@Inv.inv.{0} Complex Complex.instInv (@Nat.cast.{0} Complex Complex.instNatCast (Nat.card.{0} ↥(H i))))
              (∑ x,
                @dite.{1} Complex
                  (@Membership.mem.{0, 0} G (@Subgroup.{0} G inst)
                    (@SetLike.instMembership.{0, 0} (@Subgroup.{0} G inst) G (@Subgroup.instSetLike.{0} G inst)) (H i)
                    (@HMul.hMul.{0, 0, 0} G G G
                      (@instHMul.{0} G
                        (@MulOne.toMul.{0} G
                          (@MulOneClass.toMulOne.{0} G
                            (@Monoid.toMulOneClass.{0} G
                              (@DivInvMonoid.toMonoid.{0} G (@Group.toDivInvMonoid.{0} G inst))))))
                      (@HMul.hMul.{0, 0, 0} G G G
                        (@instHMul.{0} G
                          (@MulOne.toMul.{0} G
                            (@MulOneClass.toMulOne.{0} G
                              (@Monoid.toMulOneClass.{0} G
                                (@DivInvMonoid.toMonoid.{0} G (@Group.toDivInvMonoid.{0} G inst))))))
                        (@Inv.inv.{0} G
                          (@InvOneClass.toInv.{0} G
                            (@DivInvOneMonoid.toInvOneClass.{0} G
                              (@DivisionMonoid.toDivInvOneMonoid.{0} G (@Group.toDivisionMonoid.{0} G inst))))
                          x)
                        g)
                      x))
                  (Classical.propDecidable
                    (@Membership.mem.{0, 0} G (@Subgroup.{0} G inst)
                      (@SetLike.instMembership.{0, 0} (@Subgroup.{0} G inst) G (@Subgroup.instSetLike.{0} G inst)) (H i)
                      (@HMul.hMul.{0, 0, 0} G G G
                        (@instHMul.{0} G
                          (@MulOne.toMul.{0} G
                            (@MulOneClass.toMulOne.{0} G
                              (@Monoid.toMulOneClass.{0} G
                                (@DivInvMonoid.toMonoid.{0} G (@Group.toDivInvMonoid.{0} G inst))))))
                        (@HMul.hMul.{0, 0, 0} G G G
                          (@instHMul.{0} G
                            (@MulOne.toMul.{0} G
                              (@MulOneClass.toMulOne.{0} G
                                (@Monoid.toMulOneClass.{0} G
                                  (@DivInvMonoid.toMonoid.{0} G (@Group.toDivInvMonoid.{0} G inst))))))
                          (@Inv.inv.{0} G
                            (@InvOneClass.toInv.{0} G
                              (@DivInvOneMonoid.toInvOneClass.{0} G
                                (@DivisionMonoid.toDivInvOneMonoid.{0} G (@Group.toDivisionMonoid.{0} G inst))))
                            x)
                          g)
                        x)))
                  (fun hx =>
                    @Units.val.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)
                      (@DFunLike.coe.{1, 1, 1}
                        (@MonoidHom.{0, 0} (↥(H i))
                          (@Units.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                          (@MulOneClass.toMulOne.{0} (↥(H i))
                            (@SubmonoidClass.toMulOneClass.{0, 0} G
                              (@Monoid.toMulOneClass.{0} G
                                (@DivInvMonoid.toMonoid.{0} G (@Group.toDivInvMonoid.{0} G inst)))
                              (@Subgroup.{0} G inst) (@Subgroup.instSetLike.{0} G inst) ⋯ (H i)))
                          (@MulOneClass.toMulOne.{0}
                            (@Units.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                            (@Units.instMulOneClass.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))))
                        (↥(H i)) (fun x => @Units.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                        (@MonoidHom.instFunLike.{0, 0} (↥(H i))
                          (@Units.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                          (@MulOneClass.toMulOne.{0} (↥(H i))
                            (@SubmonoidClass.toMulOneClass.{0, 0} G
                              (@Monoid.toMulOneClass.{0} G
                                (@DivInvMonoid.toMonoid.{0} G (@Group.toDivInvMonoid.{0} G inst)))
                              (@Subgroup.{0} G inst) (@Subgroup.instSetLike.{0} G inst) ⋯ (H i)))
                          (@MulOneClass.toMulOne.{0}
                            (@Units.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                            (@Units.instMulOneClass.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))))
                        (ψ i)
                        (@Subtype.mk.{1} G
                          (fun x =>
                            @Membership.mem.{0, 0} G (@Subgroup.{0} G inst)
                              (@SetLike.instMembership.{0, 0} (@Subgroup.{0} G inst) G
                                (@Subgroup.instSetLike.{0} G inst))
                              (H i) x)
                          (@HMul.hMul.{0, 0, 0} G G G
                            (@instHMul.{0} G
                              (@MulOne.toMul.{0} G
                                (@MulOneClass.toMulOne.{0} G
                                  (@Monoid.toMulOneClass.{0} G
                                    (@DivInvMonoid.toMonoid.{0} G (@Group.toDivInvMonoid.{0} G inst))))))
                            (@HMul.hMul.{0, 0, 0} G G G
                              (@instHMul.{0} G
                                (@MulOne.toMul.{0} G
                                  (@MulOneClass.toMulOne.{0} G
                                    (@Monoid.toMulOneClass.{0} G
                                      (@DivInvMonoid.toMonoid.{0} G (@Group.toDivInvMonoid.{0} G inst))))))
                              (@Inv.inv.{0} G
                                (@InvOneClass.toInv.{0} G
                                  (@DivInvOneMonoid.toInvOneClass.{0} G
                                    (@DivisionMonoid.toDivInvOneMonoid.{0} G (@Group.toDivisionMonoid.{0} G inst))))
                                x)
                              g)
                            x)
                          hx)))
                  fun hx => @OfNat.ofNat.{0} Complex (nat_lit 0) (@Zero.toOfNat0.{0} Complex Complex.instZero))))
info: source/BrauerAudit/Inspect.lean:6:0: 'BrauerInduction.exists_trace_eq_sum_zsmul_induced_linearCharacter' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
info: source/BrauerAudit/Inspect.lean:7:0: @ClassFunction.exists_one_eq_sum_zsmul_induced_one_of_hyperelementary : ∀ {G : Type} [inst : Group.{0} G]
  [inst_1 : Fintype.{0} G],
  ∃ k H a,
    And
      (∀ (i : Fin k),
        ∃ q,
          And (Nat.Prime q)
            (∃ C,
              And
                (@LE.le.{0} (@Subgroup.{0} G inst)
                  (@Preorder.toLE.{0} (@Subgroup.{0} G inst)
                    (@PartialOrder.toPreorder.{0} (@Subgroup.{0} G inst) (@Subgroup.instPartialOrder.{0} G inst)))
                  C (H i))
                (And (@IsCyclic.{0} (↥C) (@Subgroup.zpow.{0} G inst C))
                  (And ((Nat.card.{0} ↥C).Coprime q)
                    (And
                      (∀ (h : G),
                        @Membership.mem.{0, 0} G (@Subgroup.{0} G inst)
                            (@SetLike.instMembership.{0, 0} (@Subgroup.{0} G inst) G (@Subgroup.instSetLike.{0} G inst))
                            (H i) h →
                          ∀ (c : G),
                            @Membership.mem.{0, 0} G (@Subgroup.{0} G inst)
                                (@SetLike.instMembership.{0, 0} (@Subgroup.{0} G inst) G
                                  (@Subgroup.instSetLike.{0} G inst))
                                C c →
                              @Membership.mem.{0, 0} G (@Subgroup.{0} G inst)
                                (@SetLike.instMembership.{0, 0} (@Subgroup.{0} G inst) G
                                  (@Subgroup.instSetLike.{0} G inst))
                                C
                                (@HMul.hMul.{0, 0, 0} G G G
                                  (@instHMul.{0} G
                                    (@MulOne.toMul.{0} G
                                      (@MulOneClass.toMulOne.{0} G
                                        (@Monoid.toMulOneClass.{0} G
                                          (@DivInvMonoid.toMonoid.{0} G (@Group.toDivInvMonoid.{0} G inst))))))
                                  (@HMul.hMul.{0, 0, 0} G G G
                                    (@instHMul.{0} G
                                      (@MulOne.toMul.{0} G
                                        (@MulOneClass.toMulOne.{0} G
                                          (@Monoid.toMulOneClass.{0} G
                                            (@DivInvMonoid.toMonoid.{0} G (@Group.toDivInvMonoid.{0} G inst))))))
                                    h c)
                                  (@Inv.inv.{0} G
                                    (@InvOneClass.toInv.{0} G
                                      (@DivInvOneMonoid.toInvOneClass.{0} G
                                        (@DivisionMonoid.toDivInvOneMonoid.{0} G (@Group.toDivisionMonoid.{0} G inst))))
                                    h)))
                      (∀ (h : G),
                        @Membership.mem.{0, 0} G (@Subgroup.{0} G inst)
                            (@SetLike.instMembership.{0, 0} (@Subgroup.{0} G inst) G (@Subgroup.instSetLike.{0} G inst))
                            (H i) h →
                          ∃ n,
                            @Membership.mem.{0, 0} G (@Subgroup.{0} G inst)
                              (@SetLike.instMembership.{0, 0} (@Subgroup.{0} G inst) G
                                (@Subgroup.instSetLike.{0} G inst))
                              C
                              (@HPow.hPow.{0, 0, 0} G Nat G
                                (@instHPow.{0, 0} G Nat
                                  (@NPow.toPow.{0} G
                                    (@Monoid.toNPow.{0} G
                                      (@DivInvMonoid.toMonoid.{0} G (@Group.toDivInvMonoid.{0} G inst)))))
                                h
                                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                  (@instHPow.{0, 0} Nat Nat
                                    (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                  q n))))))))
      (∀ (g : G),
        @Eq.{1} Rat (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
          (∑ i,
            @HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul) (@Int.cast.{0} Rat Rat.instIntCast (a i))
              (@ClassFunction.induced.{0, 0} G inst inst_1 Rat Rat.instField (H i)
                (fun x => @OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) g)))
info: source/BrauerAudit/Inspect.lean:8:0: 'ClassFunction.exists_one_eq_sum_zsmul_induced_one_of_hyperelementary' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
info: source/BrauerAudit/Inspect.lean:9:0: @ClassFunction.exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem : ∀ {G : Type}
  [inst : Group.{0} G] [inst_1 : Fintype.{0} G] {p : Nat},
  Nat.Prime p →
    ∀ (A : @Subgroup.{0} G inst),
      @Subgroup.Normal.{0} G inst A →
        (∀ (a : G),
            @Membership.mem.{0, 0} G (@Subgroup.{0} G inst)
                (@SetLike.instMembership.{0, 0} (@Subgroup.{0} G inst) G (@Subgroup.instSetLike.{0} G inst)) A a →
              ∀ (b : G),
                @Membership.mem.{0, 0} G (@Subgroup.{0} G inst)
                    (@SetLike.instMembership.{0, 0} (@Subgroup.{0} G inst) G (@Subgroup.instSetLike.{0} G inst)) A b →
                  @Eq.{1} G
                    (@HMul.hMul.{0, 0, 0} G G G
                      (@instHMul.{0} G
                        (@MulOne.toMul.{0} G
                          (@MulOneClass.toMulOne.{0} G
                            (@Monoid.toMulOneClass.{0} G
                              (@DivInvMonoid.toMonoid.{0} G (@Group.toDivInvMonoid.{0} G inst))))))
                      a b)
                    (@HMul.hMul.{0, 0, 0} G G G
                      (@instHMul.{0} G
                        (@MulOne.toMul.{0} G
                          (@MulOneClass.toMulOne.{0} G
                            (@Monoid.toMulOneClass.{0} G
                              (@DivInvMonoid.toMonoid.{0} G (@Group.toDivInvMonoid.{0} G inst))))))
                      b a)) →
          (∀ (g : G),
              ∃ n,
                @Membership.mem.{0, 0} G (@Subgroup.{0} G inst)
                  (@SetLike.instMembership.{0, 0} (@Subgroup.{0} G inst) G (@Subgroup.instSetLike.{0} G inst)) A
                  (@HPow.hPow.{0, 0, 0} G Nat G
                    (@instHPow.{0, 0} G Nat
                      (@NPow.toPow.{0} G
                        (@Monoid.toNPow.{0} G (@DivInvMonoid.toMonoid.{0} G (@Group.toDivInvMonoid.{0} G inst)))))
                    g
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p n))) →
            ∀ {n : Nat}
              (ρ :
                @MonoidHom.{0, 0} G
                  (@Matrix.GeneralLinearGroup.{0, 0} (Fin n) Complex (instDecidableEqFin n) (Fin.fintype n)
                    Complex.instSemiring)
                  (@MulOneClass.toMulOne.{0} G
                    (@Monoid.toMulOneClass.{0} G (@DivInvMonoid.toMonoid.{0} G (@Group.toDivInvMonoid.{0} G inst))))
                  (@MulOneClass.toMulOne.{0}
                    (@Matrix.GeneralLinearGroup.{0, 0} (Fin n) Complex (instDecidableEqFin n) (Fin.fintype n)
                      Complex.instSemiring)
                    (@Units.instMulOneClass.{0} (Matrix.{0, 0, 0} (Fin n) (Fin n) Complex)
                      (@Semiring.toMonoid.{0} (Matrix.{0, 0, 0} (Fin n) (Fin n) Complex)
                        (@Matrix.semiring.{0, 0} (Fin n) Complex Complex.instSemiring (Fin.fintype n)
                          (instDecidableEqFin n)))))),
              ∃ k H ψ,
                ∀ (g : G),
                  @Eq.{1} Complex
                    (@Matrix.trace.{0, 0} (Fin n) Complex (Fin.fintype n) Complex.instAddCommMonoid
                      (@Units.val.{0} (Matrix.{0, 0, 0} (Fin n) (Fin n) Complex)
                        (@Semiring.toMonoid.{0} (Matrix.{0, 0, 0} (Fin n) (Fin n) Complex)
                          (@Matrix.semiring.{0, 0} (Fin n) Complex Complex.instSemiring (Fin.fintype n)
                            (instDecidableEqFin n)))
                        (@DFunLike.coe.{1, 1, 1}
                          (@MonoidHom.{0, 0} G
                            (@Matrix.GeneralLinearGroup.{0, 0} (Fin n) Complex (instDecidableEqFin n) (Fin.fintype n)
                              Complex.instSemiring)
                            (@MulOneClass.toMulOne.{0} G
                              (@Monoid.toMulOneClass.{0} G
                                (@DivInvMonoid.toMonoid.{0} G (@Group.toDivInvMonoid.{0} G inst))))
                            (@MulOneClass.toMulOne.{0}
                              (@Matrix.GeneralLinearGroup.{0, 0} (Fin n) Complex (instDecidableEqFin n) (Fin.fintype n)
                                Complex.instSemiring)
                              (@Units.instMulOneClass.{0} (Matrix.{0, 0, 0} (Fin n) (Fin n) Complex)
                                (@Semiring.toMonoid.{0} (Matrix.{0, 0, 0} (Fin n) (Fin n) Complex)
                                  (@Matrix.semiring.{0, 0} (Fin n) Complex Complex.instSemiring (Fin.fintype n)
                                    (instDecidableEqFin n))))))
                          G
                          (fun x =>
                            @Matrix.GeneralLinearGroup.{0, 0} (Fin n) Complex (instDecidableEqFin n) (Fin.fintype n)
                              Complex.instSemiring)
                          (@MonoidHom.instFunLike.{0, 0} G
                            (@Matrix.GeneralLinearGroup.{0, 0} (Fin n) Complex (instDecidableEqFin n) (Fin.fintype n)
                              Complex.instSemiring)
                            (@MulOneClass.toMulOne.{0} G
                              (@Monoid.toMulOneClass.{0} G
                                (@DivInvMonoid.toMonoid.{0} G (@Group.toDivInvMonoid.{0} G inst))))
                            (@MulOneClass.toMulOne.{0}
                              (@Matrix.GeneralLinearGroup.{0, 0} (Fin n) Complex (instDecidableEqFin n) (Fin.fintype n)
                                Complex.instSemiring)
                              (@Units.instMulOneClass.{0} (Matrix.{0, 0, 0} (Fin n) (Fin n) Complex)
                                (@Semiring.toMonoid.{0} (Matrix.{0, 0, 0} (Fin n) (Fin n) Complex)
                                  (@Matrix.semiring.{0, 0} (Fin n) Complex Complex.instSemiring (Fin.fintype n)
                                    (instDecidableEqFin n))))))
                          ρ g)))
                    (∑ i,
                      @ClassFunction.induced.{0, 0} G inst inst_1 Complex Complex.instField (H i)
                        (fun x =>
                          @dite.{1} Complex
                            (@Membership.mem.{0, 0} G (@Subgroup.{0} G inst)
                              (@SetLike.instMembership.{0, 0} (@Subgroup.{0} G inst) G
                                (@Subgroup.instSetLike.{0} G inst))
                              (H i) x)
                            (Classical.propDecidable
                              (@Membership.mem.{0, 0} G (@Subgroup.{0} G inst)
                                (@SetLike.instMembership.{0, 0} (@Subgroup.{0} G inst) G
                                  (@Subgroup.instSetLike.{0} G inst))
                                (H i) x))
                            (fun hx =>
                              @Units.val.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)
                                (@DFunLike.coe.{1, 1, 1}
                                  (@MonoidHom.{0, 0} (↥(H i))
                                    (@Units.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                                    (@MulOneClass.toMulOne.{0} (↥(H i))
                                      (@SubmonoidClass.toMulOneClass.{0, 0} G
                                        (@Monoid.toMulOneClass.{0} G
                                          (@DivInvMonoid.toMonoid.{0} G (@Group.toDivInvMonoid.{0} G inst)))
                                        (@Subgroup.{0} G inst) (@Subgroup.instSetLike.{0} G inst) ⋯ (H i)))
                                    (@MulOneClass.toMulOne.{0}
                                      (@Units.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                                      (@Units.instMulOneClass.{0} Complex
                                        (@Semiring.toMonoid.{0} Complex Complex.instSemiring))))
                                  (↥(H i))
                                  (fun x => @Units.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                                  (@MonoidHom.instFunLike.{0, 0} (↥(H i))
                                    (@Units.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                                    (@MulOneClass.toMulOne.{0} (↥(H i))
                                      (@SubmonoidClass.toMulOneClass.{0, 0} G
                                        (@Monoid.toMulOneClass.{0} G
                                          (@DivInvMonoid.toMonoid.{0} G (@Group.toDivInvMonoid.{0} G inst)))
                                        (@Subgroup.{0} G inst) (@Subgroup.instSetLike.{0} G inst) ⋯ (H i)))
                                    (@MulOneClass.toMulOne.{0}
                                      (@Units.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                                      (@Units.instMulOneClass.{0} Complex
                                        (@Semiring.toMonoid.{0} Complex Complex.instSemiring))))
                                  (ψ i)
                                  (@Subtype.mk.{1} G
                                    (fun x =>
                                      @Membership.mem.{0, 0} G (@Subgroup.{0} G inst)
                                        (@SetLike.instMembership.{0, 0} (@Subgroup.{0} G inst) G
                                          (@Subgroup.instSetLike.{0} G inst))
                                        (H i) x)
                                    x hx)))
                            fun hx =>
                            @OfNat.ofNat.{0} Complex (nat_lit 0) (@Zero.toOfNat0.{0} Complex Complex.instZero))
                        g)
info: source/BrauerAudit/Inspect.lean:10:0: 'ClassFunction.exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
Build completed successfully (10 jobs).
```

### `63b0c413-d9ca-4c8b-9b51-ac83307704f5`

```text
info: source/BrauerAudit/Bridges.lean:64:0: @BrauerAudit.matrixModel_trace.{u_1,
    u_2} : ∀ {G : Type u_1} [inst : Group.{u_1} G] {V : Type u_2} [inst_1 : AddCommGroup.{u_2} V]
  [inst_2 : Module.{0, u_2} ℂ V] [inst_3 : Module.Finite.{0, u_2} ℂ V] (ρ : Representation.{0, u_1, u_2} ℂ G V) (g : G),
  Eq.{1} (Matrix.trace.{0, 0} ↑((BrauerAudit.matrixModel.{u_1, u_2} ρ) g)) (Representation.character.{u_1, 0, u_2} ρ g)
info: source/BrauerAudit/Bridges.lean:65:0: 'BrauerAudit.matrixModel_trace' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
info: source/BrauerAudit/Bridges.lean:66:0: @BrauerAudit.smallGroup.{u_1} : ∀ {G : Type u_1} [inst : Group.{u_1} G] [Finite.{u_1 + 1} G],
  ∃ K x x_1, Nonempty.{u_1 + 1} (MulEquiv.{u_1, 0} G K)
info: source/BrauerAudit/Bridges.lean:67:0: 'BrauerAudit.smallGroup' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
info: source/BrauerAudit/Bridges.lean:68:0: @BrauerAudit.subgroupCard.{u_1,
    u_2} : ∀ {G : Type u_1} [inst : Group.{u_1} G] {K : Type u_2} [inst_1 : Group.{u_2} K] (e : MulEquiv.{u_1, u_2} G K)
  (S : Subgroup.{u_2} K),
  Eq.{1} (Nat.card.{u_1} ↥(Subgroup.comap.{u_1, u_2} (MulEquiv.toMonoidHom.{u_1, u_2} e) S)) (Nat.card.{u_2} ↥S)
info: source/BrauerAudit/Bridges.lean:69:0: 'BrauerAudit.subgroupCard' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
info: source/BrauerAudit/Bridges.lean:70:0: @BrauerAudit.inducedTransport.{u_1,
    u_2} : ∀ {G : Type u_1} [inst : Group.{u_1} G] {K : Type u_2} [inst_1 : Group.{u_2} K] [inst_2 : Fintype.{u_1} G]
  [inst_3 : Fintype.{u_2} K] (e : MulEquiv.{u_1, u_2} G K) (S : Subgroup.{u_2} K) (f : K → ℂ) (g : G),
  Eq.{1}
    (ClassFunction.induced.{u_1, 0} (Subgroup.comap.{u_1, u_2} (MulEquiv.toMonoidHom.{u_1, u_2} e) S)
      (Function.comp.{u_1 + 1, u_2 + 1, 1} f ⇑e) g)
    (ClassFunction.induced.{u_2, 0} S f (e g))
info: source/BrauerAudit/Bridges.lean:71:0: 'BrauerAudit.inducedTransport' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
info: source/BrauerAudit/Bridges.lean:72:0: @BrauerAudit.rankOneBridge.{u_1} : ∀ {G : Type u_1} [inst : Group.{u_1} G] [inst_1 : Fintype.{u_1} G],
  FiniteInducedCharacterFormulaStatement.{u_1} G →
    ∀ (S : Subgroup.{u_1} G) (χ : MonoidHom.{u_1, 0} (↥S) (Units.{0} ℂ)) (g : G),
      Eq.{1} (inducedCharacter.{0, u_1} (Sigma.mk.{u_1, u_1} S χ) g)
        (ClassFunction.induced.{u_1, 0} S
          (fun y => if hy : Membership.mem.{u_1, u_1} S y then ↑(χ (Subtype.mk.{u_1 + 1} y hy)) else 0) g)
info: source/BrauerAudit/Bridges.lean:73:0: 'BrauerAudit.rankOneBridge' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
Build completed successfully (7 jobs).
```

### `75c17d9b-4b2b-44e6-a6d0-2dc3f75e9181`

```text
info: source/BrauerAudit/API.lean:4:0: @Langlands.FiniteRep.ofRepresentation.{u_1, u_2,
    u_3} : {k : Type u_1} →
  {G : Type u_2} →
    [inst : Field.{u_1} k] →
      [inst_1 : Group.{u_2} G] →
        {V : Type u_3} →
          [inst_2 : AddCommGroup.{u_3} V] →
            [inst_3 : Module.{u_1, u_3} k V] →
              [Module.Finite.{u_1, u_3} k V] → Representation.{u_1, u_2, u_3} k G V → FDRep.{u_1, u_2} k G
info: source/BrauerAudit/API.lean:5:0: @Langlands.FiniteRep.modelEquiv.{u_1, u_2,
    u_3} : {k : Type u_1} →
  {G : Type u_2} →
    [inst : Field.{u_1} k] →
      [inst_1 : Group.{u_2} G] →
        {V : Type u_3} →
          [inst_2 : AddCommGroup.{u_3} V] →
            [inst_3 : Module.{u_1, u_3} k V] →
              [inst_4 : Module.Finite.{u_1, u_3} k V] →
                (ρ : Representation.{u_1, u_2, u_3} k G V) →
                  Representation.Equiv.{u_1, u_2, u_3, u_1} ρ
                    (FDRep.ρ.{u_1, u_2} (Langlands.FiniteRep.ofRepresentation.{u_1, u_2, u_3} ρ))
info: source/BrauerAudit/API.lean:6:0: @Langlands.FiniteRep.classOfRepresentation.{u_1, u_2,
    u_3} : {k : Type u_1} →
  {G : Type u_2} →
    [inst : Field.{u_1} k] →
      [inst_1 : Group.{u_2} G] →
        {V : Type u_3} →
          [inst_2 : AddCommGroup.{u_3} V] →
            [inst_3 : Module.{u_1, u_3} k V] →
              [Module.Finite.{u_1, u_3} k V] →
                Representation.{u_1, u_2, u_3} k G V → Langlands.FiniteRep.RepClass.{u_1, u_2} k G
info: source/BrauerAudit/API.lean:7:0: @Langlands.FiniteRep.classOfRepresentation_eq_iff.{u_1, u_2, u_3,
    u_4} : ∀ {k : Type u_1} {G : Type u_2} [inst : Field.{u_1} k] [inst_1 : Group.{u_2} G] {V : Type u_3}
  [inst_2 : AddCommGroup.{u_3} V] [inst_3 : Module.{u_1, u_3} k V] [inst_4 : Module.Finite.{u_1, u_3} k V]
  {W : Type u_4} [inst_5 : AddCommGroup.{u_4} W] [inst_6 : Module.{u_1, u_4} k W]
  [inst_7 : Module.Finite.{u_1, u_4} k W] (ρ : Representation.{u_1, u_2, u_3} k G V)
  (σ : Representation.{u_1, u_2, u_4} k G W),
  Eq.{max (u_1 + 2) (u_2 + 1)} (Langlands.FiniteRep.classOfRepresentation.{u_1, u_2, u_3} ρ)
      (Langlands.FiniteRep.classOfRepresentation.{u_1, u_2, u_4} σ) ↔
    Nonempty.{max (u_4 + 1) (u_3 + 1)} (Representation.Equiv.{u_1, u_2, u_3, u_4} ρ σ)
info: source/BrauerAudit/API.lean:8:0: @Langlands.FiniteRep.character_classOfRepresentation.{u_1, u_2,
    u_3} : ∀ {k : Type u_1} {G : Type u_2} [inst : Field.{u_1} k] [inst_1 : Group.{u_2} G] {V : Type u_3}
  [inst_2 : AddCommGroup.{u_3} V] [inst_3 : Module.{u_1, u_3} k V] [inst_4 : Module.Finite.{u_1, u_3} k V]
  (ρ : Representation.{u_1, u_2, u_3} k G V),
  Eq.{max (u_1 + 1) (u_2 + 1)}
    (Langlands.FiniteRep.character.{u_1, u_2} (Langlands.FiniteRep.classOfRepresentation.{u_1, u_2, u_3} ρ))
    (Representation.character.{u_2, u_1, u_3} ρ)
info: source/BrauerAudit/API.lean:9:0: @Langlands.FiniteRep.induceRepEquiv.{u_1,
    u_2} : {k : Type u_1} →
  {G : Type u_2} →
    [inst : Field.{u_1} k] →
      [inst_1 : Group.{u_2} G] →
        (S : Subgroup.{u_2} G) →
          [inst_2 : Subgroup.FiniteIndex.{u_2} S] →
            (V : FDRep.{u_1, u_2} k ↥S) →
              Representation.Equiv.{u_1, u_2, max u_1 u_2, u_1}
                (Representation.ind.{u_1, u_2, u_2, u_1} (Subgroup.subtype.{u_2} S) (FDRep.ρ.{u_1, u_2} V))
                (FDRep.ρ.{u_1, u_2} (Langlands.FiniteRep.induceRep.{u_1, u_2} S V))
info: source/BrauerAudit/API.lean:10:0: @Langlands.FiniteRep.character_induce_classOf.{u_1,
    u_2} : ∀ {k : Type u_1} {G : Type u_2} [inst : Field.{u_1} k] [inst_1 : Group.{u_2} G] (S : Subgroup.{u_2} G)
  [inst_2 : Subgroup.FiniteIndex.{u_2} S] (V : FDRep.{u_1, u_2} k ↥S),
  Eq.{max (u_1 + 1) (u_2 + 1)}
    (Langlands.FiniteRep.character.{u_1, u_2}
      (Langlands.FiniteRep.induce.{u_1, u_2} S (Langlands.FiniteRep.classOf.{u_1, u_2} V)))
    (Representation.character.{u_2, u_1, max u_1 u_2}
      (Representation.ind.{u_1, u_2, u_2, u_1} (Subgroup.subtype.{u_2} S) (FDRep.ρ.{u_1, u_2} V)))
info: source/BrauerAudit/API.lean:11:0: @Langlands.FiniteRep.virtualRep_exists_difference.{u_1,
    u_2} : ∀ {k : Type u_1} {G : Type u_2} [inst : Field.{u_1} k] [inst_1 : Group.{u_2} G]
  (x : Langlands.FiniteRep.VirtualRep.{u_1, u_2} k G),
  ∃ a b,
    Eq.{max (u_1 + 2) (u_2 + 1)} x
      (HSub.hSub.{max (u_1 + 1) u_2, max (u_1 + 1) u_2, max (u_1 + 1) u_2} (Langlands.FiniteRep.ofClass.{u_1, u_2} a)
        (Langlands.FiniteRep.ofClass.{u_1, u_2} b))
info: source/BrauerAudit/API.lean:12:0: @Langlands.FiniteRep.virtualCharacter_ofClass.{u_1,
    u_2} : ∀ {k : Type u_1} {G : Type u_2} [inst : Field.{u_1} k] [inst_1 : Group.{u_2} G]
  (a : Langlands.FiniteRep.RepClass.{u_1, u_2} k G),
  Eq.{max (u_1 + 1) (u_2 + 1)}
    (Langlands.FiniteRep.virtualCharacter.{u_1, u_2} (Langlands.FiniteRep.ofClass.{u_1, u_2} a))
    (Langlands.FiniteRep.character.{u_1, u_2} a)
info: source/BrauerAudit/API.lean:13:0: @Langlands.FiniteRep.mem_virtualCharacters_iff.{u_1,
    u_2} : ∀ {k : Type u_1} {G : Type u_2} [inst : Field.{u_1} k] [inst_1 : Group.{u_2} G] (f : G → k),
  Membership.mem.{max u_1 u_2, max u_1 u_2} Langlands.FiniteRep.virtualCharacters.{u_1, u_2} f ↔
    ∃ a b,
      Eq.{max (u_1 + 1) (u_2 + 1)} f
        (HSub.hSub.{max u_1 u_2, max u_1 u_2, max u_1 u_2} (Langlands.FiniteRep.character.{u_1, u_2} a)
          (Langlands.FiniteRep.character.{u_1, u_2} b))
info: source/BrauerAudit/API.lean:14:0: @Langlands.FiniteRep.character_oneDimensional.{u_1,
    u_2} : ∀ {k : Type u_1} [inst : Field.{u_1} k] {H : Type u_2} [inst_1 : Group.{u_2} H]
  (χ : MonoidHom.{u_2, u_1} H (Units.{u_1} k)) (h : H),
  Eq.{u_1 + 1} (FDRep.character.{u_1, u_2} (Langlands.FiniteRep.oneDimensional.{u_1, u_2} χ) h) ↑(χ h)
info: source/BrauerAudit/API.lean:15:0: @Langlands.FiniteRep.inducedCharacterLattice_le.{u_1,
    u_2} : ∀ {k : Type u_1} {G : Type u_2} [inst : Field.{u_1} k] [inst_1 : Group.{u_2} G]
  [inst_2 : Finite.{u_2 + 1} G],
  LE.le.{max u_1 u_2} Langlands.FiniteRep.inducedCharacterLattice.{u_1, u_2}
    Langlands.FiniteRep.virtualCharacters.{u_1, u_2}
info: source/BrauerAudit/API.lean:16:0: Langlands.FiniteRep.FiniteInducedCharacterFormulaStatement.{u_1} : (G : Type u_1) →
  [Group.{u_1} G] → [Fintype.{u_1} G] → Prop
info: source/BrauerAudit/API.lean:17:0: Langlands.FiniteRep.FiniteVirtualCharacterFaithfulnessStatement.{u_1} : (G : Type u_1) →
  [Group.{u_1} G] → [Fintype.{u_1} G] → Prop
info: source/BrauerAudit/API.lean:18:0: Langlands.FiniteRep.IntegralBrauerCharacterLatticeStatement.{u_1} : (G : Type u_1) →
  [Group.{u_1} G] → [Fintype.{u_1} G] → Prop
info: source/BrauerAudit/API.lean:19:0: Langlands.FiniteRep.IntegralBrauerSpanningStatement.{u_1} : (G : Type u_1) → [Group.{u_1} G] → [Fintype.{u_1} G] → Prop
info: source/BrauerAudit/API.lean:20:0: Finite.exists_type_univ_nonempty_mulEquiv.{u_1,
  u_2} : ∀ (G : Type u_1) [inst : Group.{u_1} G] [Finite.{u_1 + 1} G],
  ∃ G' x x_1, Nonempty.{max (u_2 + 1) (u_1 + 1)} (MulEquiv.{u_1, u_2} G G')
info: source/BrauerAudit/API.lean:21:0: @LinearMap.toMatrixAlgEquiv.{u_1, u_2,
    u_3} : {R : Type u_1} →
  [inst : CommSemiring.{u_1} R] →
    {n : Type u_2} →
      [inst_1 : Fintype.{u_2} n] →
        [inst_2 : DecidableEq.{u_2 + 1} n] →
          {M₁ : Type u_3} →
            [inst_3 : AddCommMonoid.{u_3} M₁] →
              [inst_4 : Module.{u_1, u_3} R M₁] →
                Module.Basis.{u_2, u_1, u_3} n R M₁ →
                  AlgEquiv.{u_1, u_3, max u_1 u_2} R (LinearMap.{u_1, u_1, u_3, u_3} (RingHom.id.{u_1} R) M₁ M₁)
                    (Matrix.{u_2, u_2, u_1} n n R)
info: source/BrauerAudit/API.lean:22:0: @Representation.asGroupHom.{u_1, u_2,
    u_3} : {k : Type u_1} →
  {G : Type u_2} →
    {V : Type u_3} →
      [inst : CommSemiring.{u_1} k] →
        [inst_1 : Group.{u_2} G] →
          [inst_2 : AddCommMonoid.{u_3} V] →
            [inst_3 : Module.{u_1, u_3} k V] →
              Representation.{u_1, u_2, u_3} k G V →
                MonoidHom.{u_2, u_3} G (Units.{u_3} (LinearMap.{u_1, u_1, u_3, u_3} (RingHom.id.{u_1} k) V V))
info: source/BrauerAudit/API.lean:23:0: LinearMap.trace_eq_matrix_trace.{u_1, u_2,
  u_3} : ∀ (R : Type u_1) [inst : CommSemiring.{u_1} R] {M : Type u_2} [inst_1 : AddCommMonoid.{u_2} M]
  [inst_2 : Module.{u_1, u_2} R M] {ι : Type u_3} [inst_3 : DecidableEq.{u_3 + 1} ι] [inst_4 : Fintype.{u_3} ι]
  (b : Module.Basis.{u_3, u_1, u_2} ι R M) (f : LinearMap.{u_1, u_1, u_2, u_2} (RingHom.id.{u_1} R) M M),
  Eq.{u_1 + 1} ((LinearMap.trace.{u_1, u_2} R M) f)
    (Matrix.trace.{u_3, u_1} ((LinearMap.toMatrix.{u_1, u_3, u_3, u_2, u_2} b b) f))
info: source/BrauerAudit/API.lean:24:0: @Subgroup.card_map_of_injective.{u_1,
    u_2} : ∀ {G : Type u_1} [inst : Group.{u_1} G] {H : Type u_2} [inst_1 : Group.{u_2} H] {K : Subgroup.{u_1} G}
  {f : MonoidHom.{u_1, u_2} G H},
  Function.Injective.{u_1 + 1, u_2 + 1} ⇑f → Eq.{1} (Nat.card.{u_2} ↥(Subgroup.map.{u_1, u_2} f K)) (Nat.card.{u_1} ↥K)
info: source/BrauerAudit/API.lean:25:0: @Fintype.sum_equiv.{u_1, u_2,
    u_3} : ∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : Fintype.{u_1} ι] [inst_1 : Fintype.{u_2} κ]
  [inst_2 : AddCommMonoid.{u_3} M] (e : Equiv.{u_1 + 1, u_2 + 1} ι κ) (f : ι → M) (g : κ → M),
  (∀ (x : ι), Eq.{u_3 + 1} (f x) (g (e x))) → Eq.{u_3 + 1} (∑ x, f x) (∑ x, g x)
info: source/BrauerAudit/API.lean:26:0: @Representation.char_iso.{u_1, u_2, u_3,
    u_4} : ∀ {G : Type u_1} {k : Type u_2} {V : Type u_3} {W : Type u_4} [inst : Monoid.{u_1} G]
  [inst_1 : Field.{u_2} k] [inst_2 : AddCommGroup.{u_3} V] [inst_3 : Module.{u_2, u_3} k V]
  [inst_4 : AddCommGroup.{u_4} W] [inst_5 : Module.{u_2, u_4} k W] {ρ : Representation.{u_2, u_1, u_3} k G V}
  {σ : Representation.{u_2, u_1, u_4} k G W} (φ : Representation.Equiv.{u_2, u_1, u_3, u_4} ρ σ),
  Eq.{max (u_1 + 1) (u_2 + 1)} (Representation.character.{u_1, u_2, u_3} ρ) (Representation.character.{u_1, u_2, u_4} σ)
info: source/BrauerAudit/API.lean:27:0: @BrauerInduction.exists_trace_eq_sum_zsmul_induced_linearCharacter : ∀ {G : Type} [inst : Group.{0} G]
  [inst_1 : Fintype.{0} G] {n : ℕ} (ρ : MonoidHom.{0, 0} G (Matrix.GeneralLinearGroup.{0, 0} (Fin n) ℂ)),
  ∃ k H ψ a,
    ∀ (g : G),
      Eq.{1} (Matrix.trace.{0, 0} ↑(ρ g))
        (∑ i,
          HMul.hMul.{0, 0, 0} (↑(a i))
            (HMul.hMul.{0, 0, 0} (Inv.inv.{0} ↑(Nat.card.{0} ↥(H i)))
              (∑ x,
                if hx : Membership.mem.{0, 0} (H i) (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (Inv.inv.{0} x) g) x) then
                  ↑((ψ i) (Subtype.mk.{1} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (Inv.inv.{0} x) g) x) hx))
                else 0)))
info: source/BrauerAudit/API.lean:28:0: @ClassFunction.exists_one_eq_sum_zsmul_induced_one_of_hyperelementary : ∀ {G : Type} [inst : Group.{0} G]
  [inst_1 : Fintype.{0} G],
  ∃ k H a,
    (∀ (i : Fin k),
        ∃ q,
          Nat.Prime q ∧
            ∃ C,
              LE.le.{0} C (H i) ∧
                IsCyclic.{0} ↥C ∧
                  (Nat.card.{0} ↥C).Coprime q ∧
                    (∀ (h : G),
                        Membership.mem.{0, 0} (H i) h →
                          ∀ (c : G),
                            Membership.mem.{0, 0} C c →
                              Membership.mem.{0, 0} C (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} h c) (Inv.inv.{0} h))) ∧
                      ∀ (h : G),
                        Membership.mem.{0, 0} (H i) h →
                          ∃ n, Membership.mem.{0, 0} C (HPow.hPow.{0, 0, 0} h (HPow.hPow.{0, 0, 0} q n))) ∧
      ∀ (g : G), Eq.{1} 1 (∑ i, HMul.hMul.{0, 0, 0} (↑(a i)) (ClassFunction.induced.{0, 0} (H i) (fun x => 1) g))
info: source/BrauerAudit/API.lean:29:0: @ClassFunction.exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem : ∀ {G : Type}
  [inst : Group.{0} G] [inst_1 : Fintype.{0} G] {p : ℕ},
  Nat.Prime p →
    ∀ (A : Subgroup.{0} G),
      Subgroup.Normal.{0} A →
        (∀ (a : G),
            Membership.mem.{0, 0} A a →
              ∀ (b : G), Membership.mem.{0, 0} A b → Eq.{1} (HMul.hMul.{0, 0, 0} a b) (HMul.hMul.{0, 0, 0} b a)) →
          (∀ (g : G), ∃ n, Membership.mem.{0, 0} A (HPow.hPow.{0, 0, 0} g (HPow.hPow.{0, 0, 0} p n))) →
            ∀ {n : ℕ} (ρ : MonoidHom.{0, 0} G (Matrix.GeneralLinearGroup.{0, 0} (Fin n) ℂ)),
              ∃ k H ψ,
                ∀ (g : G),
                  Eq.{1} (Matrix.trace.{0, 0} ↑(ρ g))
                    (∑ i,
                      ClassFunction.induced.{0, 0} (H i)
                        (fun x => if hx : Membership.mem.{0, 0} (H i) x then ↑((ψ i) (Subtype.mk.{1} x hx)) else 0) g)
Build completed successfully (16 jobs).
```

## Library files checked

The working files match the following published bytes at Library commit `13a081dfafb3be77f947b586115e69bcabd924c8` (also unchanged from the earlier audit baseline `05e9d802f08c814de1be8cfe174ad0e47a37c791`). Only these interfaces are needed for this comparison.

| File | SHA256 |
| --- | --- |
| `Langlands/Representation/Finite/Classes.lean` | `86e04f48592f2cf0102dae07e18a294f4a9a48bed3ce5d136d1064eb2d03e514` |
| `Langlands/Representation/Finite/Classes.md` | `a856c30fe606a40e91114a6964dbadb86f8eb380775e0ecbcd62ffe49f83b114` |
| `Langlands/Representation/Finite/Induction.lean` | `a47bdbd0a4dc8d5588efa0d4eb63ef2259fdb024e7bc4266ed23ab050298d89b` |
| `Langlands/Representation/Finite/Induction.md` | `ec98b0abc5f1cd813bcae8f37b5b295e78bb128f1c4d32ea00a41c66ef0f20c7` |
| `Langlands/Representation/Finite/Virtual.lean` | `51b214fca45871f2eb6bd16a63e3ff0e3598bd0e0aef3b0bc9ff70674722af57` |
| `Langlands/Representation/Finite/Virtual.md` | `385acbb75d8b1c3487f6f8904e5c09bd491c7ae86ab502c655bd097349d06ba7` |
| `Langlands/Representation/Finite/BrauerStatement.lean` | `b5f0c11fe40dc144fbf70de32082bcaccd1cf354a5470576605dced2d6b37277` |
| `Langlands/Representation/Finite/BrauerStatement.md` | `196495fefa55c0decbfbaaf3fe183195a157a1cc2fe2a3cb3b61dadc195b0763` |
