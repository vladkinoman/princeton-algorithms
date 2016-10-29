function hanoi(disc, src, aux, dst) {
	if (disc > 0) {
		// передвигаем n - 1 дисков на вспомогательный стержень
		hanoi(disc - 1, src, dst, aux);
		console.log('Move disc ' + disc +
			' from ' + src + ' to ' + dst);
		// передвигаем оставшиеся диски со вспомогательного на целевой стержень
		hanoi(disc - 1, aux, src, dst);
	}
}