---
title: ":rotating_light: Performance regression in #{{ env.PR_NUMBER }}"
labels: P-Performance, automated issue
---
Regression >= {{ env.NOISE_THRESHOLD }}% found during merge of: #{{ env.PR_NUMBER }}
Commit: {{ env.GIT_SHA }}
Triggered by: {{ env.WORKFLOW_URL }}