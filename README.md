# Projekat uz "Uvoda u interaktivno dokazivanje teorema"
## Algoritam HipSort - Williams
```cpp
void ubaci(int a[], int i)
{
	while (i > 0) {
		int roditelj = (i - 1) / 2;
		if (a[i] <= a[roditelj])
			return;
		swap(&a[i], &a[roditelj]);
		i = roditelj;
	}
}

void ubaciSve(int a[], int n)
{
	for (int i = 1; i < n; i++)
		ubaci(a, i);
}


void izbaci(int a[], int i, int n)
{
	while (1) {
		int najveci = i;
		int levi = 2 * i + 1;
		int desni = 2 * i + 2;
		if (levi < n && a[levi] > a[najveci])
			najveci = levi;
		if (desni < n && a[desni] > a[najveci])
			najveci = desni;
		if (najveci == i)
			return;
		swap(&a[i], &a[najveci]);
		i = najveci;
	}
}

void izbaciSve(int a[], int n)
{
	for (int i = n; i > 1; i--) {
		swap(&a[0], &a[i-1]);
		izbaci(a, 0, i-1);
	}
}


void heapSort(int a[], int n)
{
	ubaciSve(a, n);
	izbaciSve(a, n);
}
```

