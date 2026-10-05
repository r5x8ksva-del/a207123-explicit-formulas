# Audit shadow package: simulates "numpy not installed" for verification runs.
raise ModuleNotFoundError("No module named 'numpy' (blocked by final-audit verify-requirements shadow)", name='numpy')
