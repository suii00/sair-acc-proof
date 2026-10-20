import sys
s = open(sys.argv[1] if len(sys.argv) > 1 else 'description_v1.1.md', encoding='utf-8').read().rstrip('\n')
print(f"chars={len(s)} utf16_units={len(s.encode('utf-16-le'))//2} bytes={len(s.encode())} limit=10000 ok={len(s)<=10000}")
